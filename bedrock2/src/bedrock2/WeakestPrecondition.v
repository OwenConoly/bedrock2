Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics.

Section WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Implicit Types (t : io_trace) (m : mem) (l : locals).

  Definition literal v (post : word -> Prop) : Prop :=
    dlet! v := word.of_Z v in post v.
  Definition get (l : locals) (x : String.string) (post : word -> Prop) : Prop :=
    exists v, map.get l x = Some v /\ post v.
  Definition load s m a (post : word -> Prop) : Prop :=
    exists v, load s m a = Some v /\ post v.
  Definition store sz m a v (post : mem -> Prop) : Prop :=
    exists m', store sz m a v = Some m' /\ post m'.

  Definition pop_read a s addr post : Prop :=
    match a with
    | Some (cons_read s0 addr0 a') =>
        if (access_size.access_size_beq s s0 && word.eqb addr addr0)%bool
        then
          post (Some a')
        else False
    | None => post None
    | _ => False end.

  Definition pop_branch a b post : Prop :=
    match a with
    | Some (cons_branch b0 a') =>
        if (Bool.eqb b b0)%bool
        then
          post (Some a')
        else False
    | None => post None
    | _ => False end.

  Section popping.
    Context {word_ok : word.ok word}.
    
    Lemma solve_pop_read a s addr (post : _ -> Prop) :
      post a -> pop_read (with_read s addr a) s addr post.
    Proof.
      intros. cbv [pop_read]. destruct a; try apply H. simpl.
      rewrite Properties.word.eqb_eq by exact eq_refl.
      rewrite access_size.internal_access_size_dec_lb by exact eq_refl.
      simpl. assumption.
    Qed.

    Lemma solve_pop_branch a b (post : _ -> Prop) :
      post a -> pop_branch (with_branch b a) b post.
    Proof.
      intros. cbv [pop_branch]. destruct a; try apply H. simpl. rewrite Bool.eqb_reflx. assumption.
    Qed.
  End popping.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    (* conceptually, maybe it doesn't make a great deal of sense to pass in the trace, and we
       should just rewrite this function so that it's like we're always passing in a trace of nil.
       it's easier to work with this way, though. *)
    Local Notation "' x <- a | y ; f" := (match a with x => f | _ => y end)
                                           (right associativity, at level 70, x pattern).
    
    Definition expr_body rec (a : option abstract_trace) (e : Syntax.expr) (post : option abstract_trace -> word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v (post a)
      | expr.var x =>
        get l x (post a)
      | expr.op op e1 e2 =>
        rec a e1 (fun a' v1 =>
        rec a' e2 (fun a'' v2 =>
        post a'' (interp_binop op v1 v2)))
      | expr.load s e =>
        rec a e (fun a' addr =>
        pop_read a' s addr (fun a'' =>
        load s m addr (post a'')))
      | expr.inlinetable s tbl e =>
        rec a e (fun a' addr' =>
        load s (map.of_list_word tbl) addr' (post a'))
      | expr.ite c e1 e2 =>
        rec a c (fun a' b =>
        pop_branch a' (negb (word.eqb b (word.of_Z 0))) (fun a'' =>
        rec a'' (if word.eqb b (word.of_Z 0) then e2 else e1) (fun a''' v =>
        post a''' v)))
    end.
    Fixpoint expr a e := expr_body expr a e.
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

   Section WithF'.
    Context {A B T} (f: T -> A -> (T -> B -> Prop) -> Prop).
    Definition list_map'_body rec (acc : T) (xs : list A) (post : T -> list B -> Prop) : Prop :=
      match xs with
      | nil => post acc nil
      | cons x xs' =>
        f acc x (fun acc' y =>
        rec acc' xs' (fun acc'' ys' =>
        post acc'' (cons y ys')))
      end.
    Fixpoint list_map' acc xs := list_map'_body list_map' acc xs.
   End WithF'.

  (*Section WithF2.
    Context {A B C} (f: C -> A -> (C -> B -> Prop) -> Prop).
    Definition list_map2_body rec (xs : list A) (acc : C) (post : list B -> C -> Prop) : Prop :=
      match xs with
      | nil => post nil acc 
      | cons x xs' =>
        f acc x (fun y z =>
        rec xs' z (fun ys' z' =>
        post (cons y ys') z'))
      end.
    Fixpoint list_map2 xs := list_map2_body list_map2 xs.
  End WithF2.*)
  
  Section WithFunctions.
    Context (call : String.string -> io_trace -> mem -> option abstract_trace -> list word -> (io_trace -> mem -> option abstract_trace -> list word -> Prop) -> Prop).
    Definition dexpr m l a e v a' := expr m l a e (fun a'2 v2 => eq a' a'2 /\ eq v v2).
    Definition dexprs m l a es vs a' := list_map' (expr m l) a es (fun a'2 vs2 => eq a' a'2 /\ eq vs vs2).
    (*Goal (forall m l a, dexprs m l a (cons (expr.load access_size.one (expr.literal 5)) nil) = dexprs m l t nil). cbv [dexprs]. simpl. Abort.*)
    Definition cmd_body (rec:_->_->_->_->_->_->Prop) (c : cmd) (t : io_trace) (m : mem) (l : locals) (a : option abstract_trace)
             (post : io_trace -> mem -> locals -> option abstract_trace -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post t m l a
      | cmd.set x ev =>
        exists v a', dexpr m l a ev v a' /\
        dlet! l := map.put l x v in
        post t m l a'
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post t m l a
      | cmd.store sz ea ev =>
        exists addr a', dexpr m l a ea addr a' /\
        exists v a'', dexpr m l a' ev v (with_write sz addr a'') /\
        store sz m addr v (fun m =>
        post t m l a'')
      | cmd.stackalloc x n c =>
        exists f, a = with_salloc f /\
        Z.modulo n (bytes_per_word width) = 0 /\
        forall addr mStack mCombined,
          anybytes addr n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x addr in
          rec c t mCombined l (apply_salloc f addr) (fun t' mCombined' l' a' =>
          exists m' mStack',
          anybytes addr n mStack' /\ map.split mCombined' m' mStack' /\
            post t' m' l' a')
      | cmd.cond br ct cf =>
        exists v a', dexpr m l a br v (with_branch (negb (Z.eqb (word.unsigned v) 0)) a') /\
        (word.unsigned v <> 0%Z -> rec ct t m l a' post) /\
        (word.unsigned v = 0%Z -> rec cf t m l a' post)
      | cmd.seq c1 c2 =>
        rec c1 t m l a (fun t' m' l' a' => rec c2 t' m' l' a' post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->io_trace->mem->locals->option abstract_trace->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l a) /\
        (forall v t m l a, inv v t m l a ->
          exists b a', dexpr m l a e b (with_branch (negb (Z.eqb (word.unsigned b) 0)) a') /\
          (word.unsigned b <> 0%Z -> rec c t m l a' (fun t' m l a'' =>
            exists v', inv v' t' m l a'' /\ lt v' v)) /\
          (word.unsigned b = 0%Z -> post t m l a'))
      | cmd.call binds fname arges =>
        exists args a', dexprs m l a arges args a' /\ (* (call : String.string -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop) *)
        call fname t m a' args (fun t' m' a'' rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          post t' m' l' a'')
      | cmd.interact binds action arges =>
        exists mKeep mGive, map.split m mKeep mGive /\
        exists args f, dexprs m l a arges args (with_IO (mGive, action, args) f) /\ 
        ext_spec t mGive action args (fun mReceive rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, rets)) t) m' l' (apply_IO f (mReceive, rets)))
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

  Definition func call '(innames, outnames, c) (t : io_trace) (m : mem) (a : option abstract_trace) (args : list word) (post : io_trace -> mem -> option abstract_trace -> list word -> Prop) :=
      exists l, map.of_list_zip innames args = Some l /\
      cmd call c t m l a (fun t' m' l' a' =>
      list_map (get l') outnames (fun rets =>
        post t' m' a' rets)).

  Definition call_body rec (functions : list (String.string * (list String.string * list String.string * cmd.cmd)))
                (fname : String.string) (t : io_trace) (m : mem) (a : option abstract_trace) (args : list word)
                (post : io_trace -> mem -> option abstract_trace -> list word -> Prop) : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if String.eqb f fname
      then func (rec functions) decl t m a args post
      else rec functions fname t m a args post
    end.
  Fixpoint call functions := call_body call functions.

  Definition program funcs main t m l a post : Prop := cmd (call funcs) main t m l a post.
End WeakestPrecondition.
Check @cmd.
Ltac unfold1_cmd e :=
  lazymatch e with
    @cmd ?width ?BW ?word ?mem ?locals ?ext_spec ?CA ?c ?t ?m ?l ?a ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body width BW word mem locals ext_spec CA
                      (@cmd width BW word mem locals ext_spec CA) c t m l a post)
  end.
Ltac unfold1_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_cmd G in
  change G.
Check @expr. Check @expr_body.
Ltac unfold1_expr e :=
  lazymatch e with
    @expr ?width ?BW ?word ?mem ?locals ?m ?l ?a ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body width BW word mem locals m l (@expr width BW word mem locals m l) a arg post)
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
Check @list_map'. Check @list_map'_body.

Ltac unfold1_list_map' e :=
  lazymatch e with
    @list_map' ?A ?B ?T ?P ?t ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map'_body A B T P (@list_map' A B T P) t arg post)
  end.
Ltac unfold1_list_map'_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map' G in
  change G.
Check @call. Check @call_body.
Ltac unfold1_call e :=
  lazymatch e with
    @call ?width ?BW ?word ?mem ?locals ?ext_spec ?fs ?fname ?t ?m ?a ?l ?post =>
    let fs := eval hnf in fs in
    constr:(@call_body width BW word mem locals ext_spec
                       (@call width BW word mem locals ext_spec) fs fname t m a l post)
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

(* general form *)
(* trying out alternate definition with function. *)
Definition appl {A B} (x : A) (f : A -> B) := f x.
Notation "'ctfunc!' name a0 .. an '|' b0 .. bn '/' g0 .. gn '|' h0 .. hn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f,
         (forall tr mem,
             (forall a0,
                 .. (forall an,
                       (forall b0,
                           .. (forall bn,
                                 (forall g0,
                                     .. (forall gn, 
                                           (forall h0,
                                               .. (forall hn,
                                                     pre ->
                                                     WeakestPrecondition.call
                                                       functions name tr mem ((appl a0 .. (appl an (appl g0 .. (appl gn f) ..)) ..)) (cons a0 .. (cons an (cons b0 .. (cons bn nil) ..)) ..)
                                                       (fun tr' mem' a' rets =>
                                                          (exists r0,
                                                              .. (exists rn,
                                                                    rets = (cons r0 .. (cons rn nil) ..) /\
                                                                      post) ..))) ..)) ..)) ..)) ..))))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      b0 binder, bn binder,
      g0 binder, gn binder,
      h0 binder, hn binder,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

(* for swap *)
Notation "'ctfunc!' name a0 .. an '|' '/' '|' h0 .. hn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f,
         (forall tr mem,
             (forall a0,
                 .. (forall an,
                       (forall h0,
                           .. (forall hn,
                                 pre ->
                                 WeakestPrecondition.call
                                   functions name tr mem (appl a0 .. (appl an f) ..) (cons a0 .. (cons an nil) ..)
                                   (fun tr' mem' a' rets =>
                                      rets = nil /\
                                        post)) ..)) ..))))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      h0 binder, hn binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

(* for memequal *)
Notation "'ctfunc!' name a0 .. an '|' '/' '|' h0 .. hn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f,
         (forall tr mem,
             (forall a0,
                 .. (forall an,
                       (forall h0,
                           .. (forall hn,
                                 pre ->
                                 WeakestPrecondition.call
                                   functions name tr mem (appl a0 .. (appl an f) ..) (cons a0 .. (cons an nil) ..)
                                   (fun tr' mem' rets =>
                                      (exists r0,
                                          .. (exists rn,     
                                                rets = (cons r0 .. (cons rn nil) ..) /\
                                                  post) ..))) ..)) ..))))
    (at level 200,
      name at level 0,
      a0 binder, an binder,
      h0 binder, hn binder,
      r0 closed binder, rn closed binder,
      tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

(* for stackswap *)
Notation "'ctfunc!' name '|' b0 .. bn '/' '|' '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f,
         (forall tr mem,
             (forall b0,
                 .. (forall bn,
                       pre ->
                       WeakestPrecondition.call
                         functions name tr mem f (cons b0 .. (cons bn nil) ..)
                         (fun tr' mem' rets =>
                            (exists r0,
                                .. (exists rn,
                                      rets = (cons r0 .. (cons rn nil) ..) /\
                                        post) ..))) ..))))
    (at level 200,
      name at level 0,
      b0 binder, bn binder,
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
