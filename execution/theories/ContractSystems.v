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

(* Some inductive structure in which to organize contract systems *)
Context {constr : Type -> Type} {names : Type -> Type}
    {A : Type} (* to traverse constr T for any T *)
    (* some utilities *)
    {constr_find : forall {T} (place : A) (struct : constr T), option T}
    {update : forall {T} (place : A) (t : T) (struct : constr T), constr T}
    {in_constr : forall {T} (t : T) (struct : constr T), Prop}
    {accum : forall {T}, constr T -> T} (* accumulates into a single value of T *)
    (* for merging systems *)
    {inner_name : forall {T}, constr T -> names T}
    {outer_name : forall {T}, constr T -> names T}
    {merge : forall {T}, constr T -> constr T -> names T -> constr T}
    (* constr has an automorphism group *)
    {constr_permutation : forall {T}, constr T -> constr T -> Prop}
    {constr_permutation_in : forall {T} (t : T) struct struct', 
        constr_permutation struct struct' ->
        in_constr t struct -> in_constr t struct'}
    (* functions between systems : constr is functorial wrt ^^ *)
    {constr_funct : forall {T T'}, (T -> T') -> (constr T -> constr T')}
    {constr_funct_names : forall {T T'}, (T -> T') -> (names T -> names T')}
    {constr_funct_A : forall {T T'}, (T -> T') -> (A -> A)}
    {constr_find_funct : forall {T T'} (f : T -> T') place struct,
        constr_find (constr_funct_A f place) (constr_funct f struct) = 
        option_map f (constr_find place struct)}
    {update_funct : forall {T T'} (f : T -> T') place t struct, 
        update (constr_funct_A f place) (f t) (constr_funct f struct) = 
        constr_funct f (update place t struct)}
    {in_constr_funct : forall {T T'} (f : T -> T') t struct,
        in_constr t struct -> in_constr (f t) (constr_funct f struct)}
    {inner_name_funct : forall {T T'} (f : T -> T') struct,
        constr_funct_names f (inner_name struct) = inner_name (constr_funct f struct)}
    {outer_name_funct : forall {T T'} (f : T -> T') struct,
        constr_funct_names f (outer_name struct) = outer_name (constr_funct f struct)}
    {merge_funct : forall {T T'} (f : T -> T') struct1 struct2 name,
        merge (constr_funct f struct1) (constr_funct f struct2) (constr_funct_names f name) = 
        constr_funct f (merge struct1 struct2 name)}.


(** We define a system of contracts *)
Section SystemDefinition.

(** To talk about systems we need a data structure *)
Record GeneralizedContract := {
    addr : Address ; (* an affiliated address *)
    wc : WeakContract ; (* wc representation, to deal with polymorphism *)
}.

(** A system of contracts consists of nodes and (directed) edges
    should reduce down to one contract ... Singleton G *)
Definition ContractSystem := constr GeneralizedContract.

Definition sys_deployed bstate (sys : constr GeneralizedContract) : Prop :=
    forall G,
    in_constr GeneralizedContract G sys ->
    env_contracts bstate (addr G) = Some (wc G).

(** System state  *)
Definition GeneralizedState : Type := constr (option SerializedValue).

Definition sys_state (bstate : ChainState) (sys : ContractSystem) : GeneralizedState := 
    constr_funct GeneralizedContract (option SerializedValue)
    (fun (gc : GeneralizedContract) => env_contract_states bstate (addr gc))
    sys.

(** A msg to a system of contracts is a message and an indicator of which contract receives the msg *)
Record GeneralizedMsg := {
    msg : option SerializedValue ;
    place : A ; (* the index of *which* contract gets called *)
}.

(* The receive function of a contract system *)
Definition gen_receive
    (sys : ContractSystem)
    (c : Chain)
    (ctx : ContractCallContext)
    (g_st : GeneralizedState) (* state *)
    (g_msg : GeneralizedMsg) (* message *) :
    result (GeneralizedState * list ActionBody) SerializedValue := 
    match constr_find GeneralizedContract (place g_msg) sys with 
    | Some gc => 
        match constr_find (option SerializedValue) (place g_msg) g_st with 
        | Some st_op => 
            match st_op with 
            | Some st => 
                match wc_receive (wc gc) c ctx st (msg g_msg) with 
                | Ok (new_st, new_acts) => 
                    Ok (update (option SerializedValue) (place g_msg) (Some new_st) g_st, new_acts)
                | Err e => Err e
                end
            | None => Err (serialize tt)
            end
        | None => Err (serialize tt) (* todo .. is this ok? *)
        end
    | None => Err (serialize tt) (* todo .. is this ok? *)
    end.

(* 
Definition gen_receive
    (sys : constr WeakContract)
    (c : Chain)
    (ctx : ContractCallContext)
    (g_st : GeneralizedState) (* state *)
    (g_msg : GeneralizedMsg) (* message *) :
    result (GeneralizedState * list ActionBody) SerializedValue :=
    do wc <- constr_find WeakContract (place g_msg) sys;
    do st_op <- constr_find (option SerializedValue) (place g_msg) g_st;
    match st_op with
    | Some st =>
        do (new_st, new_acts) <- wc_receive wc c ctx st (msg g_msg);
        ret (update (option SerializedValue) (place g_msg) (Some new_st) g_st, new_acts)
    | None => Err (serialize tt)
    end.
*)

End SystemDefinition.


(** Operations on Systems of Contracts *)
Section SystemOperations.

(** Two contract systems can be merged *)
Section SystemMerge.

(* TODO use inner/outer names, merge semantics *)
Definition system_merge_inner : ContractSystem -> ContractSystem -> ContractSystem := todo.
Definition system_merge_outer : ContractSystem -> ContractSystem -> ContractSystem := todo.

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
(* TODO quotient over a path ... ? *)

End SystemQuotient.

End SystemOperations.


(** We define various ways in which systems of contracts can be considered equivalent *)
Section ContractSystemEquivalence.

(** "strong equivalence" : bit by bit equivalence component morphisms which 
    mimics the data structure of the system of contracts : graph equivalence *)
Section StrongEquivalence.

Definition sys_eq (sys1 sys2 : ContractSystem) : Prop := 
    constr_permutation GeneralizedContract sys1 sys2.

End StrongEquivalence.


(** "weak equivalence" : there is an "equivalence of meta-contracts" *)
(* - another chained list that captures evolving state for weak morphisms *)
Section Isomorphic.

Definition wc_iso (W1 W2 : WeakContract) : Prop := todo.

Record gc_iso (G1 G2 : GeneralizedContract) := {
    gc_addr_iso : addr G1 = addr G2 ;
    gc_wc_iso : wc_iso (wc G1) (wc G2) ;
}.

Definition gc_iso_op (g1 g2 : option GeneralizedContract) : Prop := 
    match g1 with 
    | Some G1 => 
        match g2 with | Some G2 => gc_iso G1 G2 | None => False end 
    | None => False 
    end.

Definition sys_weq (sys1 sys2 : ContractSystem) : Prop := 
    forall place,
    gc_iso_op (constr_find GeneralizedContract place sys1) (constr_find GeneralizedContract place sys2).

End Isomorphic.


(** Systems of contracts are equivalent by bisimulation *)
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
        (* init morph *)

        (* step *)
        sysstep_morph : forall gstate1 gstate2,
            SystemStep sys1 gstate1 gstate2 -> 
            SystemStep sys2 (st_gstate_morph gstate1) (st_gstate_morph gstate2) ;
    }.


Record AccumTraceMorphism (sys1 sys2 : ContractSystem) := 
    build_compressed_st_morph {
        (* state morph *)
        st_state_morph : SerializedValue -> SerializedValue ; 
        (* init *)
        (* step *)
        c_sysstep_morph : forall gstate1 gstate2,
    }.

End SystemTrace.

End Bisimulation.


End ContractSystemEquivalence.


(** An API to go from (strong) contracts to a contract system *)
Section ContractToSystem.



End ContractSystem.




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