(** Contract Morphisms:
    A contract morphism f : C1 -> C2 is a formal, structural relationship between contracts C1 and C2 
    It consists of:
    1. Functions between contract types:
        setup_morph : Setup1 -> Setup1
        msg_morph   : Msg1   -> Msg1
        state_morph : State1 -> State1
        error_morph : Error1 -> Error1
    2. Proofs of coherence:
       Using the functions, we can transform inputs to C1 into inputs to C2,
       and outputs of C1 into outputs of C2.
       We should end up at the same outputs of C2 no matter what order we do 
       that transformation in.

    In particular, this gives us a notion of an isomorphism of contracts, from which we 
    can derive the notion of a bisimulation of contracts.
*)

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
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

(** The definition *)
Record ContractMorphism 
    (C1 : Contract Setup1 Msg1 State1 Error1) 
    (C2 : Contract Setup2 Msg2 State2 Error2) := 
    build_contract_morphism {
        (* the components of a morphism f *)
        setup_morph : Setup1 -> Setup2 ;
        msg_morph   : Msg1   -> Msg2   ;
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
            receive C2 c ctx (state_morph st) (option_map msg_morph op_msg) ; 
}.

End MorphismDefinition.

Section MorphismUtils.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

Definition init_coherence_prop  
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2)
    (setup_morph : Setup1 -> Setup2)
    (state_morph : State1 -> State2)
    (error_morph : Error1 -> Error2) :=
    forall c ctx s, 
    result_functor state_morph error_morph 
        (init C1 c ctx s) = 
    init C2 c ctx (setup_morph s).

Definition recv_coherence_prop
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2)
    (msg_morph : Msg1 -> Msg2)
    (state_morph : State1 -> State2)
    (error_morph : Error1 -> Error2) :=
    forall c ctx st op_msg, 
    result_functor (fun '(st, l) => (state_morph st, l)) error_morph 
        (receive C1 c ctx st op_msg) = 
    receive C2 c ctx (state_morph st) (option_map msg_morph op_msg).


Definition coherence_prop 
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2)
    (setup_morph : Setup1 -> Setup2)
    (msg_morph   : Msg1   -> Msg2)
    (state_morph : State1 -> State2)
    (error_morph : Error1 -> Error2) :=
    (forall c ctx s, 
    result_functor state_morph error_morph 
        (init C1 c ctx s) = 
    init C2 c ctx (setup_morph s)) /\ 
    (forall c ctx st op_msg, 
    result_functor (fun '(st, l) => (state_morph st, l)) error_morph 
        (receive C1 c ctx st op_msg) = 
    receive C2 c ctx (state_morph st) (option_map msg_morph op_msg)).

End MorphismUtils.


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
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Proposition eq_cm : 
    forall (f g : ContractMorphism C1 C2),
    (* if the components are equal ... *)
    (setup_morph C1 C2 f) = (setup_morph C1 C2 g) -> 
    (msg_morph C1 C2 f) = (msg_morph C1 C2 g) -> 
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
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
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
Definition compose_cm (g : ContractMorphism C2 C3) (f : ContractMorphism C1 C2) : 
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
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        `{Serializable Setup4} `{Serializable Msg4} `{Serializable State4} `{Serializable Error4}
        { C1 : Contract Setup1 Msg1 State1 Error1 } 
        { C2 : Contract Setup2 Msg2 State2 Error2 }
        { C3 : Contract Setup3 Msg3 State3 Error3 }
        { C4 : Contract Setup4 Msg4 State4 Error4 }.

(** Composition with the Identity morphism is trivial *)
Proposition compose_id_cm_left (f : ContractMorphism C1 C2) :
    compose_cm (id_cm C2) f = f.
Proof.
    now apply eq_cm.
Qed.

Proposition compose_id_cm_right (f : ContractMorphism C1 C2) :
    compose_cm f (id_cm C1) = f.
Proof.
    now apply eq_cm.
Qed.

(** Composition is associative *)
Proposition compose_cm_assoc
    (f : ContractMorphism C1 C2) 
    (g : ContractMorphism C2 C3) 
    (h : ContractMorphism C3 C4) :
    compose_cm h (compose_cm g f) =
    compose_cm (compose_cm h g) f.
Proof.
    now apply eq_cm.
Qed.

End MorphismCompositionResults.


(** We will treat various type of contract morphisms, starting with isomorphisms. *)
Section IsomorphismDefinition.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
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
    compose_cm g f = id_cm C1 /\
    compose_cm f g = id_cm C2.

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
    -   unfold is_iso_cm, compose_cm, id_cm.
        now intro H_iso.
Qed.

End IsomorphismDefinition.


Section Isomorphisms.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

(** An equality predicate on contracts *)
Definition contracts_isomorphic 
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) : Prop := 
    exists (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1),
    is_iso_cm f g.

Context `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        `{Serializable Setup4} `{Serializable Msg4} `{Serializable State4} `{Serializable Error4}
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
    is_iso_cm (compose_cm g1 f1) (compose_cm f2 g2).
Proof.
    unfold is_iso_cm.
    intros iso_f iso_g. 
    destruct iso_f as [iso_f1 iso_f2].
    destruct iso_g as [iso_g1 iso_g2].
    split; rewrite compose_cm_assoc.
    -   rewrite <- (compose_cm_assoc g1 g2 f2).
        rewrite iso_g1. 
        now rewrite (compose_id_cm_right f2).
    -   rewrite <- (compose_cm_assoc f2 f1 g1).
        rewrite iso_f2. 
        now rewrite (compose_id_cm_right g1).
Qed.

End Isomorphisms.

(** Now, onto injections *)
Section Injections.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Definition is_inj {A B : Type} (f : A -> B) : Prop := 
    forall (a a' : A), f a = f a' -> a = a'.

(* A morphism is an embedding if it embeds the message and storage types *)
Definition is_inj_cm (f : ContractMorphism C1 C2) : Prop := 
    is_inj (msg_morph C1 C2 f) /\
    is_inj (state_morph C1 C2 f).

Definition contract_embeds : Prop := 
    exists (f : ContractMorphism C1 C2), is_inj_cm f.

End Injections.


(** Finally, we treat surjections, or quotients *)
Section Surjections.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Definition is_surj {A B : Type} (f : A -> B) : Prop := 
    forall (b : B), exists (a : A), f a = b.

Definition is_surj_cm (f : ContractMorphism C1 C2) : Prop :=
    is_surj (msg_morph C1 C2 f) /\
    is_surj (state_morph C1 C2 f).

Definition contract_surjects : Prop := 
    exists (f : ContractMorphism C1 C2), is_surj_cm f.

End Surjections.


Section Exactness.
(** Extend the contract's type so it can be the recipient of a morphism. *)
Section PointedContract.
Context `{Serializable Setup} `{Serializable Msg} `{Serializable State} `{Serializable Error}.

Definition Msg' := (Msg + unit)%type.

Definition receive' 
    (C : Contract Setup Msg State Error)
    (c : Chain) 
    (ctx : ContractCallContext) 
    (st : State) 
    (op_msg : option Msg') : result (State  * list ActionBody) Error := 
    match op_msg with 
    | None => receive C c ctx st None 
    | Some msg' => 
        match msg' with 
        | inl msg => receive C c ctx st (Some msg) 
        | inr _ => Ok (st, nil)
        end 
    end.

Definition pointed_contract (C : Contract Setup Msg State Error) := 
    build_contract (init C) (receive' C).

End PointedContract.



(* TODO formally encode the notion of exactness here. *)



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


Definition is_genesis_state (C : Contract Setup Msg State Error) (init_cstate : State) : Prop := 
    exists init_chain init_ctx init_setup, 
    init C init_chain init_ctx init_setup = Ok init_cstate.

Definition cstate_reachable (C : Contract Setup Msg State Error) (cstate : State) : Prop := 
    exists init_cstate,
    (* init_cstate is a valid initial cstate *)
    is_genesis_state C init_cstate /\
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


Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
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
    destruct f as [setup_morph msg_morph state_morph error_morph init_coherence recv_coherence].
    set (f := {|
        setup_morph := setup_morph;
        msg_morph   := msg_morph;
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
    destruct f as [setup_morph msg_morph state_morph error_morph init_coherence recv_coherence].
    set (f := {|
        setup_morph := setup_morph;
        msg_morph   := msg_morph;
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


Section ContractTraceMorphism.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}.

(* *)
Record ContractTraceMorphism
    (C1 : Contract Setup1 Msg1 State1 Error1)
    (C2 : Contract Setup2 Msg2 State2 Error2) := 
    build_ct_morph {
        (* a function *)
        ct_state_morph : State1 -> State2 ;
        (* init state C1 -> init state C2 *)
        genesis_fixpoint : forall init_cstate,
            is_genesis_state C1 init_cstate ->
            is_genesis_state C2 (ct_state_morph init_cstate) ;
        (* coherence *)
        cstep_morph : forall state1 state2,
            ContractStep C1 state1 state2 ->
            ContractStep C2 (ct_state_morph state1) (ct_state_morph state2) ;
    }.

End ContractTraceMorphism.


Section IdentityCTMorphism.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}.

(* The Identity CT Morphism *)
Definition id_genesis_fixpoint_nopq (C : Contract Setup1 Msg1 State1 Error1)
    init_cstate (gen_C : is_genesis_state C init_cstate) :
    is_genesis_state C (id init_cstate) := gen_C.

Definition id_genesis_fixpoint (C : Contract Setup1 Msg1 State1 Error1) : forall init_cstate,
    is_genesis_state C init_cstate ->
    is_genesis_state C (id init_cstate).
Proof. auto. Defined.

Definition id_cstep_morph_nopq (C : Contract Setup1 Msg1 State1 Error1)
(state1 : State1) (state2 : State1) (step : ContractStep C state1 state2) :
ContractStep C (id state1) (id state2) := step.

Definition id_cstep_morph (C : Contract Setup1 Msg1 State1 Error1) : forall state1 state2,
    ContractStep C state1 state2 ->
    ContractStep C (id state1) (id state2).
Proof. auto. Defined.

Definition id_ctm (C : Contract Setup1 Msg1 State1 Error1) : ContractTraceMorphism C C := {| 
    ct_state_morph := id ; 
    genesis_fixpoint := id_genesis_fixpoint C ;
    cstep_morph := id_cstep_morph C ;
|}.

End IdentityCTMorphism.


(* Equality *)
Section EqualityOfCTMorphisms.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} {C2 : Contract Setup2 Msg2 State2 Error2}.

(* TODO not true *)
Proposition eq_ctm (f g : ContractTraceMorphism C1 C2) :
    (ct_state_morph C1 C2 f) = (ct_state_morph C1 C2 g) ->
    f = g.
Admitted.

End EqualityOfCTMorphisms.


Section CTMorphismComposition.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}
        {C3 : Contract Setup3 Msg3 State3 Error3}.


Definition genesis_compose_nopq (m2 : ContractTraceMorphism C2 C3) (m1 : ContractTraceMorphism C1 C2)
    init_cstate (gen_C1 : is_genesis_state C1 init_cstate) :
    is_genesis_state C3 (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) init_cstate) :=
  match m2 with
  | build_ct_morph _ _ _ gen_fix2 step2 =>
      match m1 with
      | build_ct_morph _ _ _ gen_fix1 step1 =>
          gen_fix2 _ (gen_fix1 _ gen_C1)
      end
  end.

Definition genesis_compose (m2 : ContractTraceMorphism C2 C3) (m1 : ContractTraceMorphism C1 C2) : 
    forall init_cstate,
    is_genesis_state C1 init_cstate ->
    is_genesis_state C3 (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) init_cstate).
Proof.
    destruct m2 as [cmorph2 gen_fix2 step2].
    destruct m1 as [cmorph1 gen_fix1 step1].
    intros * gen_C1.
    now apply gen_fix1, gen_fix2 in gen_C1.
Defined.

Definition cstep_compose_nopq (m2 : ContractTraceMorphism C2 C3) (m1 : ContractTraceMorphism C1 C2)
    state1 state2 (step : ContractStep C1 state1 state2) :
    ContractStep C3
        (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) state1)
        (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) state2) :=
  match m2 with
  | build_ct_morph _ _ _ _ step2 =>
      match m1 with
      | build_ct_morph _ _ _ _ step1 =>
          step2 _ _ (step1 _ _ step)
      end
  end.

Definition cstep_compose (m2 : ContractTraceMorphism C2 C3) (m1 : ContractTraceMorphism C1 C2) : 
    forall state1 state2,
    ContractStep C1 state1 state2 ->
    ContractStep C3 
        (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) state1) 
        (compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) state2).
Proof.
    destruct m2 as [cmorph2 gen_fix2 step2].
    destruct m1 as [cmorph1 gen_fix1 step1].
    intros * step.
    apply step2.
    now apply step1.
Defined.

Definition compose_ctm
    (m2 : ContractTraceMorphism C2 C3)
    (m1 : ContractTraceMorphism C1 C2) : ContractTraceMorphism C1 C3 := 
{| 
    ct_state_morph := compose (ct_state_morph C2 C3 m2) (ct_state_morph C1 C2 m1) ; 
    genesis_fixpoint := genesis_compose m2 m1 ;
    cstep_morph := cstep_compose m2 m1 ;
|}.

End CTMorphismComposition.


Section CTMorphismCompositionResults.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        `{Serializable Setup4} `{Serializable Msg4} `{Serializable State4} `{Serializable Error4}
        { C1 : Contract Setup1 Msg1 State1 Error1 } 
        { C2 : Contract Setup2 Msg2 State2 Error2 }
        { C3 : Contract Setup3 Msg3 State3 Error3 }
        { C4 : Contract Setup4 Msg4 State4 Error4 }.

(* Composition associative *)
Proposition compose_ctm_assoc 
    (f : ContractTraceMorphism C1 C2)
    (g : ContractTraceMorphism C2 C3)
    (h : ContractTraceMorphism C3 C4) : 
    compose_ctm h (compose_ctm g f) = 
    compose_ctm (compose_ctm h g) f.
Proof.
    now destruct f, g, h.
Qed.

(* Composition with the Identity is Trivial *)
Proposition compose_id_ctm_left (f : ContractTraceMorphism C1 C2) :
    compose_ctm (id_ctm C2) f = f.
Proof.
    now destruct f.
Qed.

Proposition compose_id_ctm_right (f : ContractTraceMorphism C1 C2) :
    compose_ctm f (id_ctm C1) = f.
Proof.
    now destruct f.
Qed.

End CTMorphismCompositionResults.

Section LiftingTheorem.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

Definition lift_genesis (f : ContractMorphism C1 C2) : 
    forall init_cstate,
        is_genesis_state C1 init_cstate ->
        is_genesis_state C2 (state_morph C1 C2 f init_cstate).
Proof.
    destruct f as [setup_morph msg_morph state_morph error_morph i_coh r_coh].
    cbn.
    intros * genesis. 
    unfold is_genesis_state in *.
    destruct genesis as [c [ctx [s init_coh]]].
    exists c, ctx, (setup_morph s).
    rewrite <- i_coh.
    unfold result_functor.
    now destruct (init C1 c ctx s).
Defined.

Definition lift_cstep_morph (f : ContractMorphism C1 C2) : 
    forall state1 state2,
        ContractStep C1 state1 state2 ->
        ContractStep C2 
            (state_morph C1 C2 f state1) 
            (state_morph C1 C2 f state2).
Proof.
    destruct f as [setup_morph msg_morph state_morph error_morph i_coh r_coh].
    cbn.
    intros * step.
    destruct step as [seq_chain seq_ctx seq_msg seq_new_acts recv_step].
    apply (build_contract_step C2 (state_morph state1) (state_morph state2) seq_chain seq_ctx (option_map msg_morph seq_msg) seq_new_acts).
    rewrite <- r_coh.
    unfold result_functor.
    destruct (receive C1 seq_chain seq_ctx state1 seq_msg);
    try destruct t;
    now inversion recv_step.
Defined.

(** Lifting Theorem *)
Definition cm_lift_ctm (f : ContractMorphism C1 C2) : ContractTraceMorphism C1 C2 :=
    build_ct_morph C1 C2 (state_morph C1 C2 f) (lift_genesis f) (lift_cstep_morph f).

End LiftingTheorem.


Section LiftingTheoremComposition.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        `{Serializable Setup3} `{Serializable Msg3} `{Serializable State3} `{Serializable Error3}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}
        {C3 : Contract Setup3 Msg3 State3 Error3}.

(** Id lifts to Id *)
Proposition cm_lift_ctm_id : 
    cm_lift_ctm (id_cm C1) = id_ctm C1.
Proof.
    now apply eq_ctm.
Qed.

(** Compositions lift to compositions *)
Proposition cm_lift_ctm_compose 
    (g : ContractMorphism C2 C3) (f : ContractMorphism C1 C2) : 
    cm_lift_ctm (compose_cm g f) = 
    compose_ctm (cm_lift_ctm g) (cm_lift_ctm f).
Proof.
    apply eq_ctm.
    now unfold compose_ctm.
Qed.

End LiftingTheoremComposition.


Section ContractBisimulation.
Context `{Serializable Setup1} `{Serializable Msg1} `{Serializable State1} `{Serializable Error1}
        `{Serializable Setup2} `{Serializable Msg2} `{Serializable State2} `{Serializable Error2}
        {C1 : Contract Setup1 Msg1 State1 Error1} 
        {C2 : Contract Setup2 Msg2 State2 Error2}.

(* A bisimulation of contracts, or an isomorphism of contract traces *)
Definition is_iso_ctm 
    (m1 : ContractTraceMorphism C1 C2) (m2 : ContractTraceMorphism C2 C1) := 
    compose_ctm m2 m1 = id_ctm C1 /\
    compose_ctm m1 m2 = id_ctm C2.

(** Contract Isomorphism -> Contract Trace Isomorphism *)
Proposition ciso_to_ctiso (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1) :
    is_iso_cm f g -> is_iso_ctm (cm_lift_ctm f) (cm_lift_ctm g).
Proof.
    unfold is_iso_cm, is_iso_ctm.
    intro iso_cm.
    destruct iso_cm as [iso_cm_l iso_cm_r].
    rewrite <- (cm_lift_ctm_compose g f).
    rewrite <- (cm_lift_ctm_compose f g).
    rewrite iso_cm_l.
    rewrite iso_cm_r.
    now repeat rewrite cm_lift_ctm_id.
Qed.

(** An equivalence of contracts is a pair of contract morphisms that lift to an isomorphism of 
        contract traces (a bisimulation). *)
Definition is_equiv_cm (f : ContractMorphism C1 C2) (g : ContractMorphism C2 C1) : Prop := 
    is_iso_ctm (cm_lift_ctm f) (cm_lift_ctm g).

End ContractBisimulation.


End ContractMorphisms.