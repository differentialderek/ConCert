(* Systems of Contracts *)
From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Sets.Ensembles.
From Coq Require Import ZArith.
From Coq Require Import ProofIrrelevance.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractMorphisms.

Import ListNotations.

Axiom todo : forall {A}, A.


(** Notation for a system of contracts, encoded as graphs, inspired by Milner's bigraphs *)
Section ContractSystem.
Context {Base : ChainBase}.

(** The fundamental building block of a system: a contract and its address *)
Record GeneralizedContract := {
    gc_addr : Address ; (* an affiliated address *)
    gc_wc : WeakContract ; (* wc representation, to deal with polymorphism *)
}.

(** The definition of a contract's Place Graph *)
Section PlaceGraph.

(* an inductive definition of trees *)
Section NTree.

Inductive ntree (T : Type) : Type :=
| Leaf : ntree T
| Node : T -> list (ntree T) -> ntree T.

(** Utils *)
Fixpoint replace_at_index {T : Type} (n : nat) (new_elem : T) (l : list T) : list T :=
  match l, n with
  | nil, _ => nil
  | _ :: tl, 0 => new_elem :: tl
  | hd :: tl, S n' => hd :: replace_at_index n' new_elem tl
  end.

(* Update a tree at a given index, which can be at a node or a leaf *)
Fixpoint update_ntree_at_index {T : Type} (tree : ntree T) (value : T) (leaf_index : list nat) : ntree T :=
  match tree, leaf_index with
  | Leaf _, nil => Node T value nil
  | Leaf _, _ :: _ => tree (* Cannot add a node at a leaf that does not exist *)
  | Node _ v children, nil => Node T value children (* Reached the desired leaf *)
  | Node _ v children, i :: is =>
      match List.nth_error children i with
      | Some child => Node T v (replace_at_index i (update_ntree_at_index child value is) children)
      | None => tree (* Invalid leaf index *)
      end
  end.

(* Merge semantics: add a tree to a given leaf *)
Fixpoint add_tree_at_leaf {T} (orig append : ntree T) (leaf_index : list nat) : ntree T :=
    match orig, leaf_index with
    | Leaf _, nil => append
    | Leaf _, _ :: _ => orig (* Cannot add a tree at a leaf that does not exist *)
    | Node _ v children, nil => orig (* Must add only at a leaf *)
    | Node _ v children, i :: is =>
        match List.nth_error children i with
        | Some child => Node T v (replace_at_index i (add_tree_at_leaf child append is) children)
        | None => orig (* Invalid leaf index *)
        end
    end.

(* find the leaves of a tree *)
Definition find_leaf_indices {T : Type} (tree : ntree T) (prefix : list nat) : list (list nat) := todo. (*
Fixpoint find_leaf_indices {T : Type} (tree : ntree T) (prefix : list nat) : list (list nat) := todo.
    match tree with 
    | Leaf _ => t (* we've reached a leaf *)
    | Node _ v children => 
        List.fold_left 
        (fun (prefix' : list (list nat)) (child : ntree T) : list (list nat) => 
            List.fold_left
            (fun (l1 l2 : list (list nat)) => l1 ++ l2)
            (find_leaf_indices child prefix)
            [])
        children
        prefix
    end.
*)

Fixpoint ntree_find_node {T} (leaf_index : list nat) (tree : ntree T) : option T :=
    match tree, leaf_index with 
    | Leaf _, nil => None (* The index was for a leaf *)
    | Leaf _, _ :: _ => None (* Cannot find a node that does not exist *)
    | Node _ v children, nil => Some v (* Reached the desired node *)
    | Node _ v children, i :: is =>
        match List.nth_error children i with
        | Some child => ntree_find_node is child (* Iterate *)
        | None => None (* Invalid leaf index *)
        end
    end.

Definition empty_ntree {T} := Leaf T.

Definition singleton_ntree {T} (t : T) := Node T t nil.

Definition in_ntree {T} (t : T) (tree : ntree T) : Prop := 
    exists leaf_index, ntree_find_node leaf_index tree = Some t.

(* Given an accumulating function and a starting point, iterate over the tree *)
Fixpoint ntree_accum {T} (tree : ntree T) (accum : T -> T -> T) (t : T) : T :=
    match tree with 
    | Leaf _ => t (* we've reached a leaf *)
    | Node _ v children => 
        List.fold_left 
        (fun (t' : T) (child : ntree T) => accum (ntree_accum child accum t) t')
        children
        (accum v t)
    end.
(*
Compute (ntree_accum 
    (Node nat 1 [singleton_ntree 2 ; singleton_ntree 4 ; singleton_ntree 5])
    (fun (a b : nat) => a + b)
    0).

Compute 
    find_leaf_indices
    (Node nat 1 [singleton_ntree 2 ; singleton_ntree 4 ; singleton_ntree 5])
    [1;2;3].
*)


(** Functoriality *)
Fixpoint ntree_funct {T T'} (f : T -> T') (tree : ntree T) : ntree T' := 
    match tree with 
    | Leaf _ => Leaf T' 
    | Node _ v children => 
        Node T' (f v) (List.map (fun child => ntree_funct f child) children)
    end.

Lemma ntree_find_funct {T T'} (f : T -> T') (index : list nat) (tree : ntree T) : 
    ntree_find_node index (ntree_funct f tree) = 
    option_map f (ntree_find_node index tree).
Proof.
    unfold ntree_find_node, ntree_funct.
    cbn.
    destruct tree, index; auto.
Admitted.

Lemma ntree_update_funct {T T'} (f : T -> T') index t tree : 
    update_ntree_at_index (ntree_funct f tree) (f t) index = 
    ntree_funct f (update_ntree_at_index tree t index).
Admitted.

Lemma in_ntree_funct {T T'} (f : T -> T') t tree :
    in_ntree t tree -> in_ntree (f t) (ntree_funct f tree).
Proof.
    intro in_tree.
    destruct in_tree as [index is_in].
    unfold in_ntree.
    exists index.
    rewrite ntree_find_funct.
    now rewrite is_in.
Qed.


(** Permutations *)
Definition NTree_Permutation {T} : ntree T -> ntree T -> Prop := todo.

Lemma intree_permutation_in {T} t (ntree1 ntree2 : ntree T) : 
    NTree_Permutation ntree1 ntree2 -> 
    (in_ntree t ntree1 <-> in_ntree t ntree2).
Proof.
    intro premute.
    split.
    (* -> *)
    -   admit.
    (* <- *)
    -   admit.
Admitted.

End NTree.

End PlaceGraph.


(** Edges in the link graph are given by contract calls *)
Section LinkGraph.

(* the system's graph *)
Definition call_to call : option Address := 
    match call with 
    | act_transfer _ _ => None 
    | act_call addr _ _ => Some addr 
    | act_deploy _ _ _ => None 
    end.

(* The type of edges *)
Record LinkGraphEdges (G1 G2 : GeneralizedContract) : Type := {
    e_chain : Chain ; 
    e_ctx : ContractCallContext ; 
    e_prvstate : SerializedValue ; (* prev state *)
    e_msg : option SerializedValue ; (* msg *)
    e_newstate : SerializedValue ; (* new state *)
    e_nacts : list ActionBody ;
    linking_act : ActionBody ; (* the action that links the two contracts *)
    (* there is some transaction for which G1 calls G2 *)
    e_recv_some : 
        (* this is a successful call *)
        wc_receive (gc_wc G1) e_chain e_ctx e_prvstate e_msg = Ok (e_newstate, e_nacts) /\
        (* which emits the transaction linking_act, *)
        List.In linking_act e_nacts /\ 
        (* and it is a call to G2 *)
        call_to linking_act = Some (gc_addr G2) ;
}.

(* edges can be composed if they are sequential transactions *)
Definition edges_compose G1 G2 G3 (e1 : LinkGraphEdges G1 G2) (e2 : LinkGraphEdges G2 G3) := 
    match linking_act G1 G2 e1 with 
    | act_call _ _ msg => e_msg G2 G3 e2 = Some msg
    | _ => False
    end.

End LinkGraph.


(** A system of contracts is a (list of) place graphs, 
    endowed automatically with the link graph structure *)
Section SystemDefinition.

(* A system of contracts is presented by its place graph;
    it inherits the link graph automatically *)
Definition ContractSystem := ntree GeneralizedContract.

(** System state *)
Definition GeneralizedState : Type := ntree (option SerializedValue).

(* the system state is constructed with the same inductive structure as the system *)
Definition sys_state (bstate : ChainState) (sys : ContractSystem) : GeneralizedState := 
    ntree_funct
    (fun (gc : GeneralizedContract) => env_contract_states bstate (gc_addr gc))
    sys.

(* use sys_accum to compress the state into a single value *) (* TODO remove "serialize tt" somehow 
Definition sys_state_compressed (bstate : ChainState) (sys : ContractSystem) : option SerializedValue :=
    ntree_accum
    (sys_state bstate sys)
    (fun s1 s2 => 
        match s1, s2 with 
        | Some x1, Some x2 => Some (serialize (x1, x2))
        | None, _ => s2 
        | _, None => s1
        end)
    (Some (serialize tt)).
*)

(** System interface *)
Record GeneralizedMsg := {
    msg : option SerializedValue ;
    place : list nat ; (* the index of *which* contract gets called *)
}.

(* move from Generalized State to Generalized State *)
Definition sys_receive (sys : ContractSystem)
    (c : Chain)
    (ctx : ContractCallContext)
    (g_st : GeneralizedState) (* state *)
    (g_msg : GeneralizedMsg) (* message *) :
    result (GeneralizedState * list ActionBody) SerializedValue := 
    match ntree_find_node (place g_msg) sys with 
    | Some gc => 
        match ntree_find_node (place g_msg) g_st with 
        | Some st_op => 
            match st_op with 
            | Some st => 
                match wc_receive (gc_wc gc) c ctx st (msg g_msg) with 
                | Ok (new_st, new_acts) => 
                    Ok (update_ntree_at_index g_st (Some new_st) (place g_msg), new_acts)
                | Err e => Err e
                end
            | None => Err (serialize tt)
            end
        | None => Err (serialize tt)
        end
    | None => Err (serialize tt)
    end.

End SystemDefinition.


(** Contract System Utils *)
Section SystemUtils.

(* a system is deployed *)
Definition sys_deployed bstate (sys : ContractSystem) : Prop :=
    forall G,
    in_ntree G sys ->
    env_contracts bstate (gc_addr G) = Some (gc_wc G).

(* the notion of the initial state of a system *)
Definition is_genesis_state_wc W init_cstate : Prop := 
    exists init_chain init_ctx init_setup, 
    wc_init W init_chain init_ctx init_setup = Ok init_cstate.

(* a better version of this perhaps? *)
Definition is_genesis_gstate_sys sys gstate : Prop :=
    forall place,
    ((exists G, ntree_find_node place sys = Some G) <->
     (exists st, ntree_find_node place gstate = Some (Some st))) /\
    (forall place G st, 
        ntree_find_node place sys = Some G ->
        ntree_find_node place gstate = Some (Some st) ->
        is_genesis_state_wc (gc_wc G) st).    

(* some propositions relating to system morphisms *)
Definition sys_genesis_prop sys1 sys2 
    (gstate_morph : GeneralizedState -> GeneralizedState) : Prop :=
    forall gstate,
        is_genesis_gstate_sys sys1 gstate -> 
        is_genesis_gstate_sys sys2 (gstate_morph gstate).

Definition sys_coherence_prop sys1 sys2 
    (gstate_morph : GeneralizedState -> GeneralizedState)
    (gmsg_morph : GeneralizedMsg -> GeneralizedMsg)
    (gerror_morph : SerializedValue -> SerializedValue) : Prop := 
    forall c ctx gst gmsg,
        result_functor (fun '(gst, l) => (gstate_morph gst, l)) gerror_morph
            (sys_receive sys1 c ctx gst gmsg) = 
        sys_receive sys2 c ctx (gstate_morph gst) (gmsg_morph gmsg).

End SystemUtils.


Section SystemMorphism.

(* a morphism of systems of contracts *)
Record SystemMorphism sys1 sys2 := 
    build_sys_morphism {
        (* component morphisms *)
        gstate_morph : GeneralizedState -> GeneralizedState ;
        gmsg_morph : GeneralizedMsg -> GeneralizedMsg ;
        gerror_morph : SerializedValue -> SerializedValue ;
        (* init coherence analogue *)
        sys_genesis : forall gstate,
            is_genesis_gstate_sys sys1 gstate ->
            is_genesis_gstate_sys sys2 (gstate_morph gstate) ;
        (* recv coherence analogue *)
        sys_coherence : forall c ctx gst gmsg,
            result_functor (fun '(gst, l) => (gstate_morph gst, l)) gerror_morph
                (sys_receive sys1 c ctx gst gmsg) =
            sys_receive sys2 c ctx (gstate_morph gst) (gmsg_morph gmsg) ;
}.

Proposition eq_sm {sys1 sys2} (f g : SystemMorphism sys1 sys2) :
    gstate_morph sys1 sys2 f = gstate_morph sys1 sys2 g -> 
    gmsg_morph sys1 sys2 f = gmsg_morph sys1 sys2 g -> 
    gerror_morph sys1 sys2 f = gerror_morph sys1 sys2 g -> 
    f = g.
Proof.
    intros gst_eq gmsg_eq gerr_eq.
    destruct f, g.
    simpl in *.
    subst.
    f_equal; apply proof_irrelevance.
Qed.

Definition compose_sm {sys1 sys2 sys3} 
    (g : SystemMorphism sys2 sys3) (f : SystemMorphism sys1 sys2) : SystemMorphism sys1 sys3.
Proof.
    destruct g, f.
    apply (build_sys_morphism sys1 sys3 
        (compose gstate_morph0 gstate_morph1)
        (compose gmsg_morph0 gmsg_morph1)
        (compose gerror_morph0 gerror_morph1)).
    -   intros * is_gen.
        now apply sys_genesis0, sys_genesis1.
    -   intros.
        cbn.
        rewrite <- (sys_coherence0 c ctx (gstate_morph1 gst) (gmsg_morph1 gmsg)).
        rewrite <- (sys_coherence1 c ctx gst gmsg).
        unfold result_functor.
        now destruct (sys_receive sys1 c ctx gst gmsg).
Defined.

Proposition compose_sm_assoc {sys1 sys2 sys3 sys4}
    (f : SystemMorphism sys1 sys2)
    (g : SystemMorphism sys2 sys3)
    (h : SystemMorphism sys3 sys4) : 
    compose_sm h (compose_sm g f) = 
    compose_sm (compose_sm h g) f.
Proof.
    now apply eq_sm; unfold compose_sm; destruct f, g, h; cbn.
Qed.

Definition id_sm sys : SystemMorphism sys sys.
Proof.
    apply (build_sys_morphism sys sys id id id); auto.
    intros.
    unfold result_functor.
    simpl.
    now destruct (sys_receive sys c ctx gst gmsg).
Qed.

Definition is_iso_sm {sys1 sys2} (f : SystemMorphism sys1 sys2) (g : SystemMorphism sys2 sys1) :=
    compose_sm g f = id_sm sys1 /\
    compose_sm f g = id_sm sys2.

Definition sys_isomorphic sys1 sys2 : Prop := 
    exists (f : SystemMorphism sys1 sys2) (g : SystemMorphism sys2 sys1),
    is_iso_sm f g.

End SystemMorphism.


(** We define various ways in which systems of contracts can be considered equivalent *)
Section ContractSystemEquivalence.

(** Firstly, a permutation is a strong notion of equality -- they are essentially "identical" *)
Definition sys_eq (sys1 sys2 : ContractSystem) : Prop := 
    NTree_Permutation sys1 sys2.

(** Secondly, systems are isomorphic iff they are isomorphic at every place *)
Section PlaceIsomorphic.

Record gc_iso (G1 G2 : GeneralizedContract) := {
    gc_addr_iso : gc_addr G1 = gc_addr G2 ;
    gc_wc_iso : wc_isomorphic (gc_wc G1) (gc_wc G2) ;
}.

Definition gc_iso_op (g1 g2 : option GeneralizedContract) : Prop := 
    match g1 with 
    | Some G1 => 
        match g2 with 
        | Some G2 => gc_iso G1 G2 
        | None => True 
        end 
    | None => 
        match g2 with 
        | Some G2 => False
        | None => True 
        end
    end.

(* the contracts of sys1 and sys2 are isomorphic at every place *)
Definition sys_place_isomorphic (sys1 sys2 : ContractSystem) : Prop := 
    forall place,
    gc_iso_op (ntree_find_node place sys1) (ntree_find_node place sys2).

(* CONJECTURE *)
Proposition place_iso_equiv : forall sys1 sys2,
    sys_place_isomorphic sys1 sys2 <->
    sys_isomorphic sys1 sys2.
Admitted.

End PlaceIsomorphic.


(** Thirdly, systems of contracts can be equivalent by bisimulation *)
Section Bisimulation.

(** The notion of a system's trace *)
Section SystemTrace.
Record SystemStep (sys : ContractSystem) (st1 st2 : GeneralizedState) := 
    build_system_step {
    sys_chain : Chain ; 
    sys_ctx : ContractCallContext ; 
    sys_gmsg : GeneralizedMsg ; 
    sys_new_acts : list ActionBody ;
    (* receive is called successfully *)
    sys_recv_some : sys_receive sys sys_chain sys_ctx st1 sys_gmsg = Ok (st2, sys_new_acts) ;
}.

Definition SystemTrace (sys : ContractSystem) :=
    ChainedList GeneralizedState (SystemStep sys).

End SystemTrace.

(** Morphism of system traces *)
Record SystemTraceMorphism (sys1 sys2 : ContractSystem) := 
    build_st_morph {
        (* state morphs, parameterized by states *)
        st_gstate_morph : GeneralizedState -> GeneralizedState ;
        (* some sort of init morph? *)
        st_genesis_fixpoint : forall (init_gstate : GeneralizedState),
            is_genesis_gstate_sys sys1 init_gstate ->
            is_genesis_gstate_sys sys2 (st_gstate_morph init_gstate) ;
        (* step *)
        sys_step_morph : forall gstate1 gstate2,
            SystemStep sys1 gstate1 gstate2 -> 
            SystemStep sys2 (st_gstate_morph gstate1) (st_gstate_morph gstate2) ;
    }.

(* the identity system trace morphism *)
Definition id_stm (sys : ContractSystem) : SystemTraceMorphism sys sys.
Proof. now apply (build_st_morph sys sys id). Defined.

(* composition *)
Definition compose_stm {sys1 sys2 sys3 : ContractSystem}
    (m2 : SystemTraceMorphism sys2 sys3) (m1 : SystemTraceMorphism sys1 sys2) : 
    SystemTraceMorphism sys1 sys3.
Proof.
    apply (build_st_morph sys1 sys3 
        (compose (st_gstate_morph sys2 sys3 m2) (st_gstate_morph sys1 sys2 m1))).
    -   intros * gen_state1.
        apply (st_genesis_fixpoint sys2 sys3 m2).
        now apply (st_genesis_fixpoint sys1 sys2 m1).
    -   intros * sys_step.
        apply (sys_step_morph sys2 sys3 m2).
        now apply (sys_step_morph sys1 sys2 m1).
Defined.

(* a strong bisimulation *)
Definition is_iso_stm {sys1 sys2 : ContractSystem}
    (m1 : SystemTraceMorphism sys1 sys2) (m2 : SystemTraceMorphism sys2 sys1) :=
    compose_stm m2 m1 = id_stm sys1 /\ 
    compose_stm m1 m2 = id_stm sys2.

Definition sm_lift_stm {sys1 sys2} 
    (f : SystemMorphism sys1 sys2) : SystemTraceMorphism sys1 sys2.
Proof.
    apply (build_st_morph sys1 sys2 (gstate_morph sys1 sys2 f) (sys_genesis sys1 sys2 f)).
    intros * s_step.
    destruct s_step.
    apply (build_system_step sys2 
        (gstate_morph sys1 sys2 f gstate1) 
        (gstate_morph sys1 sys2 f gstate2) 
        sys_chain0 
        sys_ctx0 
        (gmsg_morph sys1 sys2 f sys_gmsg0)
        sys_new_acts0).
    rewrite <- (sys_coherence sys1 sys2 f).
    now rewrite sys_recv_some0.
Defined.

Lemma sm_lift_stm_id {sys} : sm_lift_stm (id_sm sys) = id_stm sys.
Admitted.

Lemma sm_lift_stm_compose {sys1 sys2 sys3}
    (g : SystemMorphism sys2 sys3)
    (f : SystemMorphism sys1 sys2) : 
    sm_lift_stm (compose_sm g f) = 
    compose_stm (sm_lift_stm g) (sm_lift_stm f).
Admitted.

Proposition sys_iso_to_st_iso {sys1 sys2} 
    (f : SystemMorphism sys1 sys2) (g : SystemMorphism sys2 sys1) : 
    is_iso_sm f g -> is_iso_stm (sm_lift_stm f) (sm_lift_stm g).
Proof.
    intro iso_sm.
    unfold is_iso_sm, is_iso_stm in *.
    destruct iso_sm as [iso_sm_l iso_sm_r].
    split.
    -   rewrite <- sm_lift_stm_compose.
        rewrite iso_sm_l.
        now rewrite sm_lift_stm_id.
    -   rewrite <- sm_lift_stm_compose.
        rewrite iso_sm_r.
        now rewrite sm_lift_stm_id.
Qed.


(* TODO use "accum" somehow? 
Record SystemTraceMorphism' (sys1 sys2 : ContractSystem) := 
    build_st_morph' {
        (* state morphs, parameterized by states *)
        st_gstate_morph' : GeneralizedState -> GeneralizedState ;
        sys_step_morph' : forall gstate1 gstate2,
            SystemStep sys1 gstate1 gstate2 -> 
            SystemStep sys2 (st_gstate_morph' gstate1) (st_gstate_morph' gstate2) ;
        sys_state_sync : forall (gstate1 gstate2 : GeneralizedState),
            sys_accum gstate1 = sys_accum gstate2 ->
            sys_accum (st_gstate_morph' gstate1) = sys_accum (st_gstate_morph' gstate2) ;
    }.
*)

End Bisimulation.


End ContractSystemEquivalence.


(** Operations on Systems of Contracts *)
Section SystemOperations.

(* Merges already taken care of *)

(** System quotient *)
Section SystemQuotient.



(** Equivalence modulo edges ..? *)
(* quotient over a path ... ? *)

(* TODO *)
(* THIS DEFINES A NEW SYSTEM, WHERE THE INTERFACE *)

End SystemQuotient.

End SystemOperations.


(** An API to go from (strong) contracts to a contract system *)
Section ContractToSystem.

(* singleton system *)

(* (strong) contract => singleton system *)
Definition singleton_sys_init bstate caddr : ContractSystem := 
    match env_contracts bstate caddr with 
    | Some wc => singleton_ntree {| gc_addr := caddr ; gc_wc := wc ; |} 
    | None => empty_ntree
    end.

Definition build_sys bstate sys caddr name : ContractSystem := 
    match env_contracts bstate caddr with
    | Some wc => add_tree_at_leaf sys (singleton_ntree {| gc_addr := caddr ; gc_wc := wc ; |}) name
    | None => sys 
    end.

(* from a sys_constr of addresses *)
Definition sys_init bstate (sys_caddrs : ntree Address) : ntree (option GeneralizedContract) := 
    ntree_funct
    (fun caddr => 
        match env_contracts bstate caddr with 
        | Some wc => Some {| gc_addr := caddr ; gc_wc := wc ; |}
        | None => None
        end)
    sys_caddrs.

End ContractToSystem.


(** Morphisms *)
(* should allow for the interface contract example as an equivalence ... *)
(** SHARED STATE TO SHARED STATE *)
(** SHARED INTERFACE TO SHARED INTERFACE *)
(** (similar with setup/error) *)

(* e.g. equivlant if exists permutation of lists? or permutation is equivalence? *)

(* how to naturally encode systems so that they fit into a graph structure?
    - bigraphs in Coq, formalize them as an exercise
*)


Section MultiChainContractSystem.
(** All of the above but on multiple chains *)


(** Multi-chain 
Definition MultiCSys (cbases : list ChainBase) : list Type := map CSys cbases.*)


(** Systems should have an interface:
    - a (collective) message type 
    - collective storage 
    - collective balance (this might be tricky ...)
    - a collective trace
*)



End MultiChainContractSystem.


(** Morphisms of Systems of Contracts *)
Section MultiChainContractSystemMorphism.


End MultiChainContractSystemMorphism.


End ContractSystem.