(* Systems of Contracts *)
From Coq Require Import Basics.
From Coq Require Import List.
From Coq Require Import String.
From Coq Require Import Sets.Ensembles.
From Coq Require Import ZArith.
From ConCert.Execution Require Import ChainedList.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import ContractMorphisms.

Axiom todo : forall {A}, A.


(** Notation for a system of contracts, encoded as graphs, inspired by Milner's bigraphs *)
Section ContractSystem.
Context {Base : ChainBase}.

(** Contract systems are organized via some inductive constructor, e.g. lists, trees, or forests *)
Class Sys_Constr (sys_constr : Type -> Type) := { 
    (* some utilities for sys_constr : find, update, in predicate, and accum *)
    places : Type ; (* to traverse constr T for any T, e.g. nat for constr = list *)
    constr_find : forall {T} (place : places) (struct : sys_constr T), option T ;
    update : forall {T} (place : places) (t : T) (struct : sys_constr T), sys_constr T ;
    in_constr : forall {T} (t : T) (struct : sys_constr T), Prop ;
    sys_accum : forall {T}, sys_constr T -> option T ; (* accumulates into a single value of T *)
    (* sys_constr has inner and outer merge semantics *)
    inner_names : forall {T}, sys_constr T -> Type ;
    outer_names : forall {T}, sys_constr T -> Type ;
    inner_merge : forall {T} (sys1 : sys_constr T), sys_constr T -> inner_names sys1 -> sys_constr T ;
    outer_merge : forall {T} (sys1 : sys_constr T), sys_constr T -> outer_names sys1 -> sys_constr T ;
    (* sys_constr has an automorphism group *)
    constr_permutation : forall {T}, sys_constr T -> sys_constr T -> Prop ;
    constr_permutation_in : forall {T} (t : T) struct struct', 
        constr_permutation struct struct' ->
        in_constr t struct -> in_constr t struct' ;
    (* functions between systems : sys_constr is functorial wrt most of ^^ *)
    constr_funct : forall {T T'}, (T -> T') -> (sys_constr T -> sys_constr T') ;
    constr_funct_A : forall {T T'}, (T -> T') -> (places -> places) ;
    constr_find_funct : forall {T T'} (f : T -> T') place struct,
        constr_find (constr_funct_A f place) (constr_funct f struct) = 
        option_map f (constr_find place struct) ;
    update_funct : forall {T T'} (f : T -> T') place t struct, 
        update (constr_funct_A f place) (f t) (constr_funct f struct) = 
        constr_funct f (update place t struct) ;
    in_constr_funct : forall {T T'} (f : T -> T') t struct,
        in_constr t struct -> in_constr (f t) (constr_funct f struct) ;
    (* TODO possibly add merge functoriality here too *)
}.

(* assume some system construction sys_constr *)
Context `{Sys_Constr sys_constr}.


(** We define a system of contracts *)
Section SystemDefinition.

Record GeneralizedContract := {
    addr : Address ; (* an affiliated address *)
    wc : WeakContract ; (* wc representation, to deal with polymorphism *)
}.

Definition ContractSystem := sys_constr GeneralizedContract.

Definition sys_deployed bstate (sys : ContractSystem) : Prop :=
    forall G,
    in_constr G sys ->
    env_contracts bstate (addr G) = Some (wc G).

(** System state  *)
Definition GeneralizedState : Type := sys_constr (option SerializedValue).

(* the system state is constructed with the same inductive structure as the system *)
Definition sys_state (bstate : ChainState) (sys : ContractSystem) : GeneralizedState := 
    constr_funct
    (fun (gc : GeneralizedContract) => env_contract_states bstate (addr gc))
    sys.

(* use sys_accum to compress the state into a single value *)
Definition sys_state_compressed (bstate : ChainState) (sys : ContractSystem) : option SerializedValue :=
    match sys_accum (sys_state bstate sys) with 
    | Some sys_accum => sys_accum 
    | None => None 
    end.

(** System interface *)
Record GeneralizedMsg := {
    msg : option SerializedValue ;
    place : places ; (* the index of *which* contract gets called *)
}.

(* move from Generalized State to Generalized State *)
Definition gen_receive (sys : ContractSystem)
    (c : Chain)
    (ctx : ContractCallContext)
    (g_st : GeneralizedState) (* state *)
    (g_msg : GeneralizedMsg) (* message *) :
    result (GeneralizedState * list ActionBody) SerializedValue := 
    match constr_find (place g_msg) sys with 
    | Some gc => 
        match constr_find (place g_msg) g_st with 
        | Some st_op => 
            match st_op with 
            | Some st => 
                match wc_receive (wc gc) c ctx st (msg g_msg) with 
                | Ok (new_st, new_acts) => 
                    Ok (update (place g_msg) (Some new_st) g_st, new_acts)
                | Err e => Err e
                end
            | None => Err (serialize tt)
            end
        | None => Err (serialize tt) (* todo .. is this ok? *)
        end
    | None => Err (serialize tt) (* todo .. is this ok? *)
    end.

End SystemDefinition.


(** We define various ways in which systems of contracts can be considered equivalent *)
Section ContractSystemEquivalence.

(** Firstly, a permutation is a strong notion of equality -- they are essentially "identical" *)
Definition sys_eq (sys1 sys2 : ContractSystem) : Prop := 
    constr_permutation sys1 sys2.

(** Secondly, systems are isomorphic if they are isomorphic at every place *)
Section Isomorphic.

Record gc_iso (G1 G2 : GeneralizedContract) := {
    gc_addr_iso : addr G1 = addr G2 ;
    gc_wc_iso : wc_isomorphic (wc G1) (wc G2) ;
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
Definition sys_isomorphic (sys1 sys2 : ContractSystem) : Prop := 
    forall place,
    gc_iso_op (constr_find place sys1) (constr_find place sys2).

End Isomorphic.


(** Thirdly, systems of contracts can be equivalent by bisimulation *)
Section Bisimulation.

(** The notion of a system's trace *)
Section SystemTrace.
Record SystemStep (sys : ContractSystem) (st1 st2 : GeneralizedState) := {
    sys_chain : Chain ; 
    sys_ctx : ContractCallContext ; 
    sys_gst : GeneralizedState ;
    sys_gmsg : GeneralizedMsg ; 
    sys_new_acts : list ActionBody ;
    (* receive is called successfully *)
    sys_recv_some : gen_receive sys sys_chain sys_ctx sys_gst sys_gmsg = Ok (st2, sys_new_acts) ;
}.

Definition SystemTrace (sys : ContractSystem) :=
    ChainedList GeneralizedState (SystemStep sys).

(** Morphism of system traces *)
Record SystemTraceMorphism (sys1 sys2 : ContractSystem) := 
    build_st_morph {
        (* state morphs, parameterized by states *)
        st_gstate_morph : GeneralizedState -> GeneralizedState ;
        (* some sort of init morph? *)
        (* step *)
        sysstep_morph : forall gstate1 gstate2,
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
    apply (build_st_morph sys1 sys3 (compose (st_gstate_morph sys2 sys3 m2) (st_gstate_morph sys1 sys2 m1))).
    intros.
    apply (sysstep_morph sys2 sys3 m2).
    now apply (sysstep_morph sys1 sys2 m1).
Qed.

Definition is_iso_stm {sys1 sys2 : ContractSystem}
    (m1 : SystemTraceMorphism sys1 sys2) (m2 : SystemTraceMorphism sys2 sys1) :=
    compose_stm m2 m1 = id_stm sys1 /\ 
    compose_stm m1 m2 = id_stm sys2.

End SystemTrace.


(* TODO use "accum" somehow? *)
Record SystemTraceMorphism' (sys1 sys2 : ContractSystem) := 
    build_st_morph' {
        (* state morphs, parameterized by states *)
        st_gstate_morph' : GeneralizedState -> GeneralizedState ;
        sysstep_morph' : forall gstate1 gstate2,
            SystemStep sys1 gstate1 gstate2 -> 
            SystemStep sys2 (st_gstate_morph' gstate1) (st_gstate_morph' gstate2) ;
        sys_state_sync : forall (gstate1 gstate2 : GeneralizedState),
            sys_accum gstate1 = sys_accum gstate2 ->
            sys_accum (st_gstate_morph' gstate1) = sys_accum (st_gstate_morph' gstate2) ;
    }.


End Bisimulation.


End ContractSystemEquivalence.


(** Operations on Systems of Contracts *)
Section SystemOperations.

(** Two contract systems can be merged *)
Section SystemMerge.
Definition system_merge_inner 
    (sys1 sys2 : ContractSystem) (name : inner_names sys1) : ContractSystem := 
    inner_merge sys1 sys2 name.

(* {outer_merge : forall {T} (sys1 : constr T), constr T -> outer_names sys1 -> constr T} *)
Definition system_merge_outer 
    (sys1 sys2 : ContractSystem) (name : outer_names sys1) : ContractSystem := 
    outer_merge sys1 sys2 name.

End SystemMerge.


(** System quotient *)
Section SystemQuotient.

(* the system's graph *)
Definition call_to call : option Address := 
    match call with 
    | act_transfer _ _ => None 
    | act_call addr _ _ => Some addr 
    | act_deploy _ _ _ => None 
    end.

(* The type of edges *)
Record Edges (G1 G2 : GeneralizedContract) : Type := {
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
        wc_receive (wc G1) e_chain e_ctx e_prvstate e_msg = Ok (e_newstate, e_nacts) /\
        (* which emits the transaction linking_act, *)
        List.In linking_act e_nacts /\ 
        (* and it is a call to G2 *)
        call_to linking_act = Some (addr G2) ;
}.

(* edges can be composed if they are sequential transactions *)
Definition edges_compose G1 G2 G3 (e1 : Edges G1 G2) (e2 : Edges G2 G3) := 
    match linking_act G1 G2 e1 with 
    | act_call _ _ msg => e_msg G2 G3 e2 = Some msg
    | _ => False
    end.

(** Equivalence modulo edges ..? *)
(* quotient over a path ... ? *)

(* TODO *)
(* THIS DEFINES A NEW SYSTEM, WHERE THE INTERFACE *)

End SystemQuotient.

End SystemOperations.


(** An API to go from (strong) contracts to a contract system *)
Section ContractToSystem.



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