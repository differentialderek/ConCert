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

Axiom todo : string -> forall {A}, A.


(** Notation for a system of contracts, encoded as *bigraphs* *)
Section ContractSystem.
Context {Base : ChainBase}.

Definition wc_preimage (wc : WeakContract) :=
    exists 
        (Setup Msg State Error : Type) 
        (ser_s : Serializable Setup)
        (ser_m : Serializable Msg)
        (ser_st : Serializable State)
        (ser_e : Serializable Error)
        (C : Contract Setup Msg State Error),
    wc = contract_to_weak_contract C.

Record WeakContractPreimage := {
    wc : WeakContract ; 
    wc_preim : wc_preimage wc ;
}.

(** A system of contracts is encoded as a hierarchical *tree* *)
Record ContractSystem := {
    (* a directed graph *)
}.

Definition Edges (C1 C2 : WeakContractPreimage) : Type := todo "".
    (* exists txn call to C1 which outputs txn to C2 *)
    (* forall C1 C2 : contract, *)


(** The notion of "shared state" for a CSys *)
Definition State_sys (sys : ContractSystem) : Type := todo "".
(* the product of all the states *)

(* e.g. ... *)
(* map to the contract states *)
(* fold over that to get the actual state -- multiply all states together. *)



(** The notion of "shared msg/interface" for a CSys *)
Definition Msg_sys : Type := todo "".
(* the SUM of all the msg types *)



(** Definition of a "METACONTRACT", which is the aggregated state, entrypoints,
    and **trace semantics** like with the  *)
Definition MetaContract (sys : ContractSystem) : Type := todo "".


End ContractSystem.




Section ContractSystemMorphism.


(** "strong equivalence" : bit by bit equivalence component morphisms which 
    mimics the data structure of the system of contracts : graph equivalence *)


(** "weak equivalence" : there is an "equivalence of meta-contracts" *)
(* - another chained list that captures evolving state for weak morphisms *)



(** "join metacontracts" : one metacontract, another metacontract, with an edge *)




End ContractSystemMorphism.





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