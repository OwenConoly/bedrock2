Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics.

Section WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Implicit Types (t : trace) (m : mem) (l : locals).

  (* is there a better way to include trace in postcondition? easier to work with? *)
  Definition literal v (post : word -> Prop) : Prop :=
    dlet! v := word.of_Z v in post v.
  Definition get (l : locals) (x : String.string) (post : word -> Prop) : Prop :=
    exists v, map.get l x = Some v /\ post v.
  Definition load s m a (post : word -> Prop) : Prop :=
    exists v, load s m a = Some v /\ post v.
  Definition store sz m a v (post : mem -> Prop) : Prop :=
    exists m', store sz m a v = Some m' /\ post m'.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Definition expr_body rec (e : Syntax.expr) (post : trace -> word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v (post nil)
      | expr.var x =>
        get l x (post nil)
      | expr.op op e1 e2 =>
        rec e1 (fun t1 v1 =>
        rec e2 (fun t2 v2 =>
        post (app t2 t1) (interp_binop op v1 v2)))
      | expr.load s e =>
        rec e (fun t a =>
        load s m a (post (cons (read s a) t)))
      | expr.inlinetable s tbl e =>
        rec e (fun t a =>
        load s (map.of_list_word tbl) a (post t))
      | expr.ite c e1 e2 =>
        rec c (fun t1 b => rec (if word.eqb b (word.of_Z 0) then e2 else e1) (fun t2 v =>
        post (app t2 t1) v))
    end.
    Fixpoint expr e := expr_body expr e.
  End WithMemAndLocals.

   Section WithF.
    Context {A B} (f: A -> (B -> Prop) -> Prop).
    Definition list_map_body rec (xs : list A) (post : list B -> Prop) : Prop :=
      match xs with
      | nil => post nil
      | cons x xs' =>
        f x (fun y =>
        rec xs' (fun ys' =>
        post (cons y ys')))
      end.
    Fixpoint list_map xs := list_map_body list_map xs.
   End WithF.

  Section WithF2.
    Context {A B C} (f: A -> (B -> C -> Prop) -> Prop).
    Definition list_map2_body rec (xs : list A) (post : list B -> list C -> Prop) : Prop :=
      match xs with
      | nil => post nil nil
      | cons x xs' =>
        f x (fun y z =>
        rec xs' (fun ys' zs' =>
        post (cons y ys') (cons z zs')))
      end.
    Fixpoint list_map2 xs := list_map2_body list_map2 xs.
  End WithF2.
  
  Section WithFunctions.
    Context (call : String.string -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop).
    Definition dexpr m l e v t := expr m l e (fun t' v' => eq t t' /\ eq v v'). Check dexpr.
    Definition dexprs m l es vs ts := list_map2 (expr m l) es (fun ts' vs' => eq ts ts' /\ eq vs vs'). Check dexprs. Check expr.
    Definition cmd_body (rec:_->_->_->_->_->Prop) (c : cmd) (t : trace) (m : mem) (l : locals)
             (post : trace -> mem -> locals -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post t m l
      | cmd.set x ev =>
        exists v tv, dexpr m l ev v tv /\
        dlet! l := map.put l x v in
        post (app tv t) m l
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post t m l
      | cmd.store sz ea ev =>
        exists a ta, dexpr m l ea a ta /\
        exists v tv, dexpr m l ev v tv /\
        store sz m a v (fun m =>
        post (cons (write sz a) (app tv (app ta t))) m l)
      | cmd.stackalloc x n c =>
        Z.modulo n (bytes_per_word width) = 0 /\
        forall a mStack mCombined,
          anybytes a n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x a in
          rec c t mCombined l (fun t' mCombined' l' =>
          exists m' mStack',
          anybytes a n mStack' /\ map.split mCombined' m' mStack' /\
          post t' m' l')
      | cmd.cond br ct cf =>
        exists v tv, dexpr m l br v tv /\
        (word.unsigned v <> 0%Z -> rec ct (cons (branch true) (app tv t)) m l post) /\
        (word.unsigned v = 0%Z -> rec cf (cons (branch false) (app tv t)) m l post)
      | cmd.seq c1 c2 =>
        rec c1 t m l (fun t m l => rec c2 t m l post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          exists b tb, dexpr m l e b tb /\
          (word.unsigned b <> 0%Z -> rec c (cons (branch true) (app tb t)) m l (fun t' m l =>
            exists v', inv v' t' m l /\ lt v' v)) /\
          (word.unsigned b = 0%Z -> post (cons (branch false) (app tb t)) m l))
      | cmd.call binds fname arges =>
        exists args targs, dexprs m l arges args targs /\ (* (call : String.string -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop) *)
        call fname (app (List.concat (List.rev targs)) t) m args (fun t m rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          post t m l')
      | cmd.interact binds action arges =>
        exists args targs, dexprs m l arges args targs /\
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec (app (List.concat (List.rev targs)) t) mGive action args (fun mReceive rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons (IOevent ((mGive, action, args), (mReceive, rets))) (app (List.concat (List.rev targs)) t)) m' l')
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

  Definition func call '(innames, outnames, c) (t : trace) (m : mem) (args : list word) (post : trace -> mem -> list word -> Prop) :=
      exists l, map.of_list_zip innames args = Some l /\
      cmd call c t m l (fun t m l =>
        list_map (get l) outnames (fun rets =>
        post t m rets)).

  Definition call_body rec (functions : list (String.string * (list String.string * list String.string * cmd.cmd)))
                (fname : String.string) (t : trace) (m : mem) (args : list word)
                (post : trace -> mem -> list word -> Prop) : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if String.eqb f fname
      then func (rec functions) decl t m args post
      else rec functions fname t m args post
    end.
  Fixpoint call functions := call_body call functions. Check func.

  Definition program funcs main t m l post : Prop := cmd (call funcs) main t m l post.
End WeakestPrecondition.
Check cmd.
Ltac unfold1_cmd e :=
  lazymatch e with
    @cmd ?width ?BW ?word ?mem ?locals ?ext_spec ?CA ?c ?t ?m ?l ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body width BW word mem locals ext_spec CA
                      (@cmd width BW word mem locals ext_spec CA) c t m l post)
  end.
Ltac unfold1_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_cmd G in
  change G.

Ltac unfold1_expr e :=
  lazymatch e with
    @expr ?width ?word ?mem ?locals ?m ?l ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body width word mem locals m l (@expr width word mem locals m l) arg post)
  end.
Ltac unfold1_expr_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_expr G in
  change G.

Ltac unfold1_list_map e :=
  lazymatch e with
    @list_map ?A ?B ?P ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map_body A B P (@list_map A B P) arg post)
  end.
Ltac unfold1_list_map_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map G in
  change G.

Ltac unfold1_call e :=
  lazymatch e with
    @call ?width ?BW ?word ?mem ?locals ?ext_spec ?fs ?fname ?t ?m ?l ?post =>
    let fs := eval hnf in fs in
    constr:(@call_body width BW word mem locals ext_spec
                       (@call width BW word mem locals ext_spec) fs fname t m l post)
  end.
Ltac unfold1_call_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_call G in
  change G.

Import Coq.ZArith.ZArith.

Notation "'fnspec!' name a0 .. an '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post) ..)))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  rets = nil /\ post))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        (exists r0,
                            .. (exists rn,
                                   rets = (cons r0 .. (cons rn nil) ..) /\
                                   post) ..)))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
        (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem nil
                               (fun tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post) ..)))) ..)))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        rets = nil /\ post))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem nil
                               (fun tr' mem' rets =>
                                  rets = nil /\ post))) ..))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall tr mem,
         pre ->
         WeakestPrecondition.call
           functions name tr mem nil
           (fun tr' mem' rets =>
              (exists r0,
                  .. (exists rn,
                         rets = (cons r0 .. (cons rn nil) ..) /\
                         post) ..))))
    (at level 200,
     name at level 0,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).
