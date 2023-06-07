(* A Description of Morphisms of Contracts *)

From Coq Require Import Basics.
From Coq Require Import ProofIrrelevance.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Bool.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Permutation.
From Coq Require Import RelationClasses.
From Coq Require Import Classes.Equivalence.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import BuildUtils.
From ConCert.Execution Require Import InterContractCommunication.
From ConCert.Utils Require Import RecordUpdate.

Section ContractMorphisms.
Context { Base : ChainBase }.

Definition result_functor {T T' E E' : Type} : (T -> T') -> (E -> E') -> result T E -> result T' E' :=
    fun (f_t : T -> T') (f_e : E -> E') (res : result T E) => 
    match res with | Ok t => Ok (f_t t) | Err e => Err (f_e e) end.

(** First, a definition of a Contract Morphism, which is a function between contracts *)
Section MorphismDefinition.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}.

(** The definition *)
Record ContractMorphism 
    (C1 : Contract Setup1 Msg1 State1 Error1) 
    (C2 : Contract Setup2 Msg2 State2 Error2) := {
    (* the components of a morphism f *)
    msg_morph : Msg1 -> Msg2 ;
    setup_morph : Setup1 -> Setup2 ;
    state_morph : State1 -> State2 ;
    error_morph : Error1 -> Error2 ;
    (* coherence conditions *)
    init_coherence : forall c ctx s, 
        result_functor state_morph error_morph 
            (init C1 c ctx s) = 
        init C2 c ctx (setup_morph s) ;
    recv_coherence : forall c ctx st op_msg, 
        result_functor (fun '(st, l) => (state_morph st, l)) error_morph 
            (receive C1 c ctx st op_msg) = 
        receive C2 c ctx (state_morph st) (option_map msg_morph op_msg) ; }.

End MorphismDefinition.


(** The Identity Contract Morphism *)
Section IdentityMorphism.
Context `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}.

Lemma init_coherence_id (C : Contract Setup Msg State Error) : 
    forall c ctx s,
    result_functor (@id State) (@id Error) (init C c ctx s) = 
    init C c ctx s.
Proof. 
    intros.
    unfold result_functor.
    now destruct (init C c ctx s).
Qed.

Lemma recv_coherence_id (C : Contract Setup Msg State Error) : 
    forall c ctx st op_msg, 
    result_functor 
        (fun '(st, l) => (@id State st, l)) (@id Error) 
        (receive C c ctx st op_msg) = 
    receive C c ctx (@id State st) (option_map (@id Msg) op_msg).
Proof.
    intros.
    unfold result_functor, option_map. cbn.
    destruct op_msg.
    -   now destruct (receive C c ctx st (Some m)); try destruct t.
    -   now destruct (receive C c ctx st None); try destruct t.
Qed.

(* * the identity morphism *)
Definition id_cm (C : Contract Setup Msg State Error) : ContractMorphism C C := {|
        (* components *)
        msg_morph := @id Msg ; 
        setup_morph := @id Setup ;
        state_morph := @id State ; 
        error_morph := @id Error ; 
        (* coherence conditions *)
        init_coherence := init_coherence_id C ; 
        recv_coherence := recv_coherence_id C ;
    |}.

End IdentityMorphism.

(** Deriving equality of Contract Morphisms *)
Section EqualityOfMorphisms.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Proposition eq_cm : 
    forall (f g : ContractMorphism C1 C2),
    (* if the components are equal ... *)
    (msg_morph C1 C2 f) = (msg_morph C1 C2 g) -> 
    (setup_morph C1 C2 f) = (setup_morph C1 C2 g) -> 
    (state_morph C1 C2 f) = (state_morph C1 C2 g) -> 
    (error_morph C1 C2 f) = (error_morph C1 C2 g) -> 
    (* ... then the morphisms are equal *)
    f = g.
Proof.
    intros f g.
    destruct f, g.
    cbn.
    intros msg_eq set_eq st_eq err_eq.
    subst.
    f_equal;
    apply proof_irrelevance.
Qed.

End EqualityOfMorphisms.


(** An explicit construction of the composition of two morphisms *)
Section MorphismComposition.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Msg3} `{Serializable Setup3} `{Serializable State3} `{Serializable Error3}
        { C1 : Contract Setup1 Msg1 State1 Error1 } 
        { C2 : Contract Setup2 Msg2 State2 Error2 }
        { C3 : Contract Setup3 Msg3 State3 Error3 }.

Lemma compose_init_coh (g : ContractMorphism C2 C3) (f : ContractMorphism C1 C2) : 
    let state_morph' := (compose (state_morph C2 C3 g) (state_morph C1 C2 f)) in 
    let error_morph' := (compose (error_morph C2 C3 g) (error_morph C1 C2 f)) in 
    let setup_morph' := (compose (setup_morph C2 C3 g) (setup_morph C1 C2 f)) in 
    forall c ctx s, 
        result_functor state_morph' error_morph'
            (init C1 c ctx s) = 
        init C3 c ctx (setup_morph' s).
Proof.
    intros.
    unfold setup_morph'.
    cbn.
    rewrite <- (init_coherence C2 C3 g).
    rewrite <- (init_coherence C1 C2 f).
    unfold result_functor.
    now destruct (init C1 c ctx s).
Qed.

Lemma compose_recv_coh (g : ContractMorphism C2 C3) (f : ContractMorphism C1 C2) : 
    let state_morph' := (compose (state_morph C2 C3 g) (state_morph C1 C2 f)) in 
    let error_morph' := (compose (error_morph C2 C3 g) (error_morph C1 C2 f)) in 
    let msg_morph'   := (compose (msg_morph   C2 C3 g) (msg_morph   C1 C2 f)) in 
    forall c ctx st op_msg, 
        result_functor 
            (fun '(st, l) => (state_morph' st, l)) error_morph' 
            (receive C1 c ctx st op_msg) = 
        receive C3 c ctx (state_morph' st) (option_map msg_morph' op_msg).
Proof.
    intros.
    pose proof (recv_coherence C2 C3 g).
    pose proof (recv_coherence C1 C2 f).
    unfold state_morph', msg_morph'.
    cbn.
    replace (option_map (compose (msg_morph C2 C3 g) (msg_morph C1 C2 f)) op_msg) 
    with (option_map (msg_morph C2 C3 g) (option_map (msg_morph C1 C2 f) op_msg)).
    2:{ now destruct op_msg. }
    rewrite <- H11.
    rewrite <- H12.
    unfold result_functor.
    now destruct (receive C1 c ctx st op_msg).
Qed.

(** Composition *)
Definition composition_cm (g : ContractMorphism C2 C3) (f : ContractMorphism C1 C2) : 
    ContractMorphism C1 C3 := {| 
    (* the components *)
    msg_morph   := compose (msg_morph   C2 C3 g) (msg_morph   C1 C2 f) ; 
    setup_morph := compose (setup_morph C2 C3 g) (setup_morph C1 C2 f) ; 
    state_morph := compose (state_morph C2 C3 g) (state_morph C1 C2 f) ; 
    error_morph := compose (error_morph C2 C3 g) (error_morph C1 C2 f) ; 
    (* the coherence results *)
    init_coherence := compose_init_coh g f ; 
    recv_coherence := compose_recv_coh g f ; 
    |}.

End MorphismComposition.

Section MorphismCompositionResults.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Msg3} `{Serializable Setup3} `{Serializable State3} `{Serializable Error3}
        `{Serializable Msg4} `{Serializable Setup4} `{Serializable State4} `{Serializable Error4}
        { C1 : Contract Setup1 Msg1 State1 Error1 } 
        { C2 : Contract Setup2 Msg2 State2 Error2 }
        { C3 : Contract Setup3 Msg3 State3 Error3 }
        { C4 : Contract Setup4 Msg4 State4 Error4 }.

(** Composition with the Identity morphism is trivial *)
Proposition composition_id_cm_left (f : ContractMorphism C1 C2) :
    composition_cm (id_cm C2) f = f.
Proof.
    now apply eq_cm.
Qed.

Proposition composition_id_cm_right (f : ContractMorphism C1 C2) :
    composition_cm f (id_cm C1) = f.
Proof.
    now apply eq_cm.
Qed.

(** Composition is associative *)
Proposition composition_assoc_cm
    (f : ContractMorphism C1 C2) 
    (g : ContractMorphism C2 C3) 
    (h : ContractMorphism C3 C4) :
    composition_cm h (composition_cm g f) =
    composition_cm (composition_cm h g) f.
Proof.
    now apply eq_cm.
Qed.

End MorphismCompositionResults.


(** We will treat various type of contract morphisms, starting with isomorphisms. *)
Section IsomorphismDefinition.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Definition is_iso {A B : Type} (f : A -> B) (g : B -> A) : Prop := 
    compose g f = @id A /\ compose f g = @id B.

Lemma is_iso_reflexive {A B : Type} (f : A -> B) (g : B -> A) : 
    is_iso f g -> is_iso g f.
Proof. 
    unfold is_iso. 
    intro H_is_iso. 
    now destruct H_is_iso. 
Qed.

Definition is_iso_cm (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1) : Prop :=
    composition_cm g f = id_cm C1 /\
    composition_cm f g = id_cm C2.

Lemma iso_cm_components :
    forall (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1),
    is_iso (msg_morph   C1 C2 f) (msg_morph   C2 C1 g) /\
    is_iso (setup_morph C1 C2 f) (setup_morph C2 C1 g) /\
    is_iso (state_morph C1 C2 f) (state_morph C2 C1 g) /\
    is_iso (error_morph C1 C2 f) (error_morph C2 C1 g)
    <->
    is_iso_cm f g.
Proof.
    intros f g. 
    unfold is_iso. 
    unfold iff. 
    split.
    (* -> *)
    -   intro H_iso.
        unfold is_iso_cm.
        split; now apply eq_cm.
    (* <- *)
    -   unfold is_iso_cm, composition_cm, id_cm.
        now intro H_iso.
Qed.

End IsomorphismDefinition.


Section Isomorphisms.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}.

(** An equality predicate on contracts *)
Definition contracts_isomorphic 
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) : Prop := 
    exists (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1),
    is_iso_cm f g.

Context `{Serializable Msg3} `{Serializable Setup3} `{Serializable State3} `{Serializable Error3}
        `{Serializable Msg4} `{Serializable Setup4} `{Serializable State4} `{Serializable Error4}
        { C1 : Contract Setup1 Msg1 State1 Error1 } 
        { C2 : Contract Setup2 Msg2 State2 Error2 }
        { C3 : Contract Setup3 Msg3 State3 Error3 }
        { C4 : Contract Setup4 Msg4 State4 Error4 }.

Lemma iso_cm_reflexive (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1) : 
    is_iso_cm f g -> 
    is_iso_cm g f.
Proof.
    intro H_is_iso.
    apply iso_cm_components in H_is_iso.
    apply iso_cm_components. 
    destruct H_is_iso as [H_ind_iso H_is_iso].
    do 2 (apply is_iso_reflexive in H_ind_iso;
    split; 
    try exact H_ind_iso; 
    clear H_ind_iso;
    destruct H_is_iso as [H_ind_iso H_is_iso]).
    split; now apply is_iso_reflexive.
Qed.

Lemma composition_iso_cm 
    (f1 : ContractMorphism C1 C2)
    (g1 : ContractMorphism C2 C3)
    (f2 : ContractMorphism C2 C1)
    (g2 : ContractMorphism C3 C2) :
    is_iso_cm f1 f2 -> 
    is_iso_cm g1 g2 -> 
    is_iso_cm (composition_cm g1 f1) (composition_cm f2 g2).
Proof.
    unfold is_iso_cm.
    intros iso_f iso_g. 
    destruct iso_f as [iso_f1 iso_f2].
    destruct iso_g as [iso_g1 iso_g2].
    split; rewrite composition_assoc_cm.
    -   rewrite <- (composition_assoc_cm g1 g2 f2).
        rewrite iso_g1. 
        now rewrite (composition_id_cm_right f2).
    -   rewrite <- (composition_assoc_cm f2 f1 g1).
        rewrite iso_f2. 
        now rewrite (composition_id_cm_right g1).
Qed.

End Isomorphisms.

Axiom todo : string -> forall {A}, A.
(** Now, onto injections *)
Section Injections.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Definition is_inj {A B : Type} (f : A -> B) : Prop := 
    forall (a a' : A), f a = f a' -> a = a'.

Definition is_inj_cm (f : ContractMorphism C1 C2) : Prop := 
    todo "".

Definition contract_embeds : Prop := 
    exists (f : ContractMorphism C1 C2), is_inj_cm f.

End Injections.


(** Finally, we treat surjections, or quotients *)
Section Surjections.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Definition is_surj {A B : Type} (f : A -> B) : Prop := 
    forall (b : B), exists (a : A), f a = b.

Definition is_surj_cm (f : ContractMorphism C1 C2) : Prop := todo "".

Definition contract_surjects : Prop := 
    exists (f : ContractMorphism C1 C2), is_surj_cm f.

End Surjections.

(** TODO EXACTNESS *)
Section Exactness.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Msg3} `{Serializable Setup3} `{Serializable State3} `{Serializable Error3}
        { C1 : Contract Setup1 Msg1 State1 Error1 } 
        { C2 : Contract Setup2 Msg2 State2 Error2 }
        { C3 : Contract Setup3 Msg3 State3 Error3 }.


(** TODO in light of e.g.s *)


End Exactness.


(** Morphism Induction: 
    A proof technique for contract morphisms which allows us to carry the relationship
    established by a contract morphism into contract_induction. *)
Section MorphismInduction.

(** Define the notion of a contract's trace, which is a chained list of successful
    contract calls which mimics the blockchain. *)
Section ContractTrace.
Context { Setup Msg State Error : Type }
        `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}.

(* Notions of contract state stepping forward *)
Record ContractStep (C : Contract Setup Msg State Error)
    (prev_cstate : State) (next_cstate : State) := 
    build_contract_step {
    seq_chain : Chain ;
    seq_ctx : ContractCallContext ;
    seq_msg : option Msg ;
    seq_new_acts : list ActionBody ;
    (* we can call receive successfully *)
    recv_some_step : 
        receive C seq_chain seq_ctx prev_cstate seq_msg = Ok (next_cstate, seq_new_acts) ;
}.

Definition ContractTrace (C : Contract Setup Msg State Error) := 
    ChainedList State (ContractStep C).

(* TODO some notion of reachability which involves an `init_state` to replace 
    into left_cm_induction *)

Definition cstate_reachable (C : Contract Setup Msg State Error) (cstate : State) : Prop := 
    exists init_cstate,
    (* init_cstate is a valid initial cstate *)
    (exists init_chain init_ctx init_setup, 
    init C init_chain init_ctx init_setup = Ok init_cstate) /\
    (* with a trace to cstate *)
    inhabited (ContractTrace C init_cstate cstate).

Lemma inhab_trace_trans (C : Contract Setup Msg State Error) : 
forall from mid to, 
    (ContractStep C mid to) -> 
    inhabited (ContractTrace C from mid) -> 
    inhabited (ContractTrace C from to).
Proof.
    intros from mid to step.
    apply inhabited_covariant.
    intro mid_t.
    apply (snoc mid_t step).
Qed.

End ContractTrace.


Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.


(* A theorem to use if we are inducting on C *)
(* - the relationship always exists with some parallel C' 
        - rounding down/Uranium example. *)


(** TODO a notion of it *corresponding* *)
(* f : C -> C' *)
Theorem left_cm_induction : 
    (* forall simple morphism and reachable bstate, *)
    forall (f : ContractMorphism C1 C2) bstate caddr (trace : ChainTrace empty_state bstate),
    (* where C is at caddr with state cstate, *)
    env_contracts bstate caddr = Some (C1 : WeakContract) -> 
    exists (cstate1 : State1), 
    contract_state bstate caddr = Some cstate1 /\
    (* every reachable cstate1 of C1 corresponds to a contract-reachable cstate2 of C2 ... *)
    (exists (cstate2 : State2),
    (* 1. init_cstate2 is a valid initial cstate of C'  *)
    cstate_reachable C2 cstate2 /\
    (* 2. cstate and cstate' are related by state_morph. *)
    cstate2 = state_morph C1 C2 f cstate1).
Proof.
    intros f * c_at_caddr.
    destruct f as [msg_morph setup_morph state_morph error_morph init_coherence recv_coherence].
    set (f := {|
        msg_morph := msg_morph;
        setup_morph := setup_morph;
        state_morph := state_morph;
        error_morph := error_morph;
        init_coherence := init_coherence;
        recv_coherence := recv_coherence
      |}).
    (* Prove by induction on the trace or by contract induction. *)
    contract_induction; auto.
    (* deployment *)
    -   intros.
        exists (state_morph result).
        cbn.
        split; auto.
        unfold cstate_reachable.
        exists (state_morph result).
        split.
        2:{ constructor.
            exact clnil. }
        exists chain, ctx, (setup_morph setup).
        rewrite <- (init_coherence chain ctx setup).
        destruct (init C1 chain ctx setup); 
        now try inversion init_some.
    (* non-recursive call *)
    -   intros.
        destruct IH as [cstate_prev' [cstate_reach cstate_rel]].
        destruct cstate_reach as [init_state' [init_success prev_trace]].
        destruct init_success as [init_c [init_ctx [init_s init_some']]].
        simpl in cstate_rel.
        exists (state_morph new_state).
        split; auto.
        (* reprove reachability *)
        unfold cstate_reachable.
        exists (init_state').
        split.
        +   now exists init_c, init_ctx, init_s.
        +   assert (ContractStep C2 cstate_prev' (state_morph new_state))
                as cstep.
            {   set (seq_new_state := state_morph new_state).
                set (seq_msg := option_map msg_morph msg).
                apply (build_contract_step C2 cstate_prev' seq_new_state chain ctx seq_msg new_acts).
                (* now apply coherence *)
                rewrite cstate_rel.
                unfold seq_msg.
                rewrite <- (recv_coherence chain ctx prev_state msg).
                destruct (receive C1 chain ctx prev_state msg) eqn:H_rec;
                now try inversion receive_some. }
            apply (inhab_trace_trans C2 init_state' cstate_prev' (state_morph new_state)); 
            auto.
    (* recursive call *)
    -   intros.
        destruct IH as [cstate_prev' [cstate_reach cstate_rel]].
        destruct cstate_reach as [init_state' [init_success prev_trace]].
        destruct init_success as [init_c [init_ctx [init_s init_some']]].
        simpl in cstate_rel.
        exists (state_morph new_state).
        split; auto.
        (* reprove reachability *)
        unfold cstate_reachable.
        exists (init_state').
        split.
        +   now exists init_c, init_ctx, init_s.
        +   assert (ContractStep C2 cstate_prev' (state_morph new_state))
                as cstep.
            {   set (seq_new_state := state_morph new_state).
                set (seq_msg := option_map msg_morph msg).
                apply (build_contract_step C2 cstate_prev' seq_new_state chain ctx seq_msg new_acts).
                (* now apply coherence *)
                rewrite cstate_rel.
                unfold seq_msg.
                rewrite <- (recv_coherence chain ctx prev_state msg).
                destruct (receive C1 chain ctx prev_state msg) eqn:H_rec;
                now try inversion receive_some. }
            apply (inhab_trace_trans C2 init_state' cstate_prev' (state_morph new_state)); 
            auto.
    (* solve facts *)
    -   intros.
        solve_facts.
Qed.


(* A theorem to use if we are inducting on C' *)
(* - if preimage, then relationship exists; OR reachable state => reachable state 
        - upgradeability example
        - backwards compatibility (inj)
        - bug fix (surj) *)


(** TODO a notion of grabbing an init? or do you just do that if you can? *)
(* f : C -> C' *)
Theorem right_cm_induction:
    forall (from to : State1) (f : ContractMorphism C1 C2),
    ContractTrace C1 from to ->
    ContractTrace C2 (state_morph C1 C2 f from) (state_morph C1 C2 f to).
Proof.
    intros * ctrace.
    destruct f as [msg_morph setup_morph state_morph error_morph init_coherence recv_coherence].
    set (f := {|
        msg_morph := msg_morph;
        setup_morph := setup_morph;
        state_morph := state_morph;
        error_morph := error_morph;
        init_coherence := init_coherence;
        recv_coherence := recv_coherence
      |}).
    cbn.
    induction ctrace.
    -   exact clnil.
    -   assert (ContractStep C2 (state_morph mid) (state_morph to))
        as cstep.
        {   destruct l as [s_chain s_ctx s_msg s_new_acts s_recv].
            set (seq_msg := option_map msg_morph s_msg).
            apply (build_contract_step C2 (state_morph mid) (state_morph to) s_chain s_ctx seq_msg s_new_acts).
            (* now apply coherence *)
            unfold seq_msg.
            rewrite <- (recv_coherence s_chain s_ctx mid s_msg).
            destruct (receive C1 s_chain s_ctx mid s_msg) eqn:H_rec;
            now try inversion s_recv. }
        apply (snoc IHctrace cstep).
Qed.


(* TODO : Implications if there's a contract ISOmorphism. 
    ... Can we compose these inductive rules?? *)


End MorphismInduction.


(** Equivalences of Contracts : an equivalence on just reachable states *)
Section ContractEquiv.
Context `{Serializable Msg1} `{Serializable Setup1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Msg2} `{Serializable Setup2} `{Serializable State2} `{Serializable Error2}.

(* *)
Record ContractTraceMorphism 
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) := 
    build_ct_morph {
        (* a function *)
        ct_state_morph : State1 -> State2 ;
        (* TODO init -> init *)
        (* coherence *)
        cstep_morph : forall state1 state2,
            cstate_reachable C1 state1 ->
            ContractStep C1 state1 state2 ->
            ContractStep C2 (ct_state_morph state1) (ct_state_morph state2) ;
}.

(* Identity *)
(* Equality *)
(* Composition *)

Record ContractTraceIsomorphism
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) := {
    (* todo *)
    }.

Context {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

(** Weak Equivalence : an equivalence on reachable states *)
Definition is_equivalence (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1) : Prop := 
    is_iso (msg_morph   C1 C2 f) (msg_morph   C2 C1 g) /\
    is_iso (setup_morph C1 C2 f) (setup_morph C2 C1 g) /\
    forall cstate1 cstate2,
    (* f and g are isomorphic on reachable states *)
    (cstate_reachable C1 cstate1 -> compose (state_morph C2 C1 g) (state_morph C1 C2 f) cstate1 = cstate1) /\
    (cstate_reachable C2 cstate2 -> compose (state_morph C1 C2 f) (state_morph C2 C1 g) cstate2 = cstate2).

(** Isomorphism -> Equivalence *)
Proposition iso_to_equiv_cm (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1) : 
    is_iso_cm f g -> is_equivalence f g.
Admitted.

(** equivalence -> contract trace equivalence *)
Proposition equiv_to_ctmorph (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1) :
    is_equivalence f g -> ContractTraceIsomorphism C1 C2.
Admitted.

End ContractEquiv.


End ContractMorphisms.