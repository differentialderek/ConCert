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


(** TODO:
    - A system of contracts 
        - Notion of shared state
        - Morphisms of these things 
        - Isomorphisms/Equivalences of these things 
    - A *multi-chain system* of contracts
        - repeat ^^
    - Maybe some contract operations plus nil contract .. ? Maybe
*)

Axiom todo : string -> forall {A}, A.

(** Notation for a system of contracts *)
Section ContractSystem.

(** On one single chain *)
Definition CSys (B : ChainBase) : Type := list (@WeakContract B).
(* plus contract preimages? *)


(** Multi-chain *)
Definition CSysS (B1 B2 : ChainBase) : Type := list (@WeakContract B1) * list (@WeakContract B2).


(** Systems should have an interface:
    - a (collective) message type 
    - collective storage 
    - collective balance (this might be tricky ...)
    - a collective trace
*)

End ContractSystem.


(** Morphisms of Systems of Contracts *)
Section SystemMorphism.


End SystemMorphism.


(** Equivalences of Systems of Contracts *)
Section SysEquiv.

(* first strong equiv *)

(** Some notion of **shared trace** 
    - their balances 
    - their states 
    - incoming/outgoing messages 

*)

(** Weak equivalences (just reachable) *)

End SysEquiv.



(** Multi-chain Contracts and Systems of Multi-chain Contracts *)
Section MultiChainContract.
Context {B1 B2: ChainBase}
    { Setup1 Setup2 Msg1 Msg2 State1 State2 Error1 Error2 : Type }
    `{m1_ser : Serializable Msg1} `{s1_ser : Serializable Setup1} 
    `{st1_ser : Serializable State1} `{er1_ser : Serializable Error1}
    `{m2_ser : Serializable Msg2} `{s2_ser : Serializable Setup2} 
    `{st2_ser : Serializable State2} `{er2_ser : Serializable Error2}.

(* A multi-chain contract *)
Definition MContract : Type := 
    (@Contract B1 Setup1 Msg1 State1 Error1 s1_ser m1_ser st1_ser er1_ser + 
     @Contract B2 Setup2 Msg2 State2 Error2 s2_ser m2_ser st2_ser er2_ser)%type.


(* A system of multi-chain contracts *)


(* Equivalence (both strong and weak) of multi-chain contracts *)



(* should all be a straightforward generalization of what's above *)



End MultiChainContract.













Definition pair_fun {S T S' T' : Type} 
    (f : S -> S') (g : T -> T') (x : S * T) : S' * T' :=
    let (s,t) := x in (f s, g t).
Definition pair_fun2 {S T S' T' S'' T'' : Type}
    (f : S -> S' -> S'') (g : T -> T' -> T'') (x : S * T) (y : S' * T') : S'' * T'' := 
    let (s,t) := x in let (s', t') := y in (f s s', g t t').


(** We have some interesting categorical properties, including the existence of a terminal
contract. (Note that we have not yet proved uniqueness of the terminal morphism.) 
Section TerminalContract.
Context {Base : ChainBase}.
Import ListNotations.
Set Nonrecursive Elimination Schemes.

(** State *)
Record Null_State := { null_state : unit }.

(** Msg *)
Inductive Null_Msg := 
| null_msg (n : unit).

(** Setup *)
Definition Null_Setup := option unit.

(* one canonical error message *)
Definition Null_Error := unit.

(** Init/Recv Functions *)
Definition null_init 
    (_ : Chain) 
    (_ : ContractCallContext) 
    (null_init : Null_Setup) : result Null_State Null_Error := 
        match null_init with 
        | Some _ => Ok {| null_state := tt |}
        | None => Err tt
        end.

Definition null_recv
    (_ : Chain) 
    (_ : ContractCallContext) 
    (_ : Null_State) 
    (op_msg : option Null_Msg) : 
    result (Null_State * list ActionBody) Null_Error := 
        match op_msg with 
        | Some _ => Ok ({| null_state := tt |}, [])
        | None => Err tt
        end.

(** Derive [Serializable] instances for state and messages *)
Global Instance Null_State_serializable : Serializable Null_State :=
Derive Serializable Null_State_rect<Build_Null_State>.

Global Instance Null_Msg_serializable : Serializable Null_Msg :=
Derive Serializable Null_Msg_rect<null_msg>.

(** The Terminal contract *)
Definition null_contract : Contract Null_Setup Null_Msg Null_State Null_Error := 
    build_contract null_init null_recv.

(* prove that every contract has a morphism into the terminal contract *)
Context 
    { Setup Msg State Error : Type } 
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    { C : Contract Setup Msg State Error }.

(* init morphisms *)
Definition morph_init_i (x : Chain * ContractCallContext * Setup) : Chain * ContractCallContext * Null_Setup :=
    let (x', s) := x in let (c, ctx) := x' in
    match (C.(init) c ctx s) with 
    | Ok  _ => (c, ctx, Some tt)
    | Err _ => (c, ctx, None)
    end.
Definition morph_init_o (x : result State Error) : result Null_State Null_Error := 
    match x with 
    | Ok  _ => Ok {| null_state := tt |}
    | Err _ => Err tt
    end.
Lemma null_init_commutes : init_morphs_commute C.(init) null_contract.(init) morph_init_i morph_init_o.
Proof.
    unfold init_morphs_commute. 
    intro. destruct x as [x' s]. destruct x' as [c ctx]. simpl.
    unfold uncurry_3. unfold null_init. unfold morph_init_o.
    now destruct (init C c ctx s).
Qed.

(* recv morphisms *)
Definition morph_recv_i (x : Chain * ContractCallContext * State * option Msg) : Chain * ContractCallContext * Null_State * option Null_Msg := 
    let (x', op_msg) := x in
    let (x'', st) := x' in 
    let (c, ctx) := x'' in 
    match (C.(receive) c ctx st op_msg) with 
    | Ok  _ => (c, ctx, {| null_state := tt |}, (Some (null_msg tt)))
    | Err _ => (c, ctx, {| null_state := tt |}, None)
    end.
Definition morph_recv_o (x : result (State * list ActionBody) Error) : result (Null_State * list ActionBody) Null_Error := 
    match x with 
    | Ok  _ => Ok ({| null_state := tt |}, [])
    | Err _ => Err tt 
    end.
Lemma null_recv_commutes : recv_morphs_commute C.(receive) null_contract.(receive) morph_recv_i morph_recv_o.
Proof.
    unfold recv_morphs_commute. intro.
    destruct x as [x' op_msg]. destruct x' as [x'' st]. destruct x'' as [c ctx]. simpl.
    unfold uncurry_4. unfold null_recv. unfold morph_recv_o.
    now destruct (receive C c ctx st op_msg).
Qed.

(* the terminal morphism *)
Definition null_morphism : ContractMorphism C null_contract := 
    let morph_init := {|
        init_inputs   := morph_init_i ; 
        init_outputs  := morph_init_o ;
        init_commutes := null_init_commutes ;
    |} in
    let morph_recv := {|
        recv_inputs   := morph_recv_i ;
        recv_outputs  := morph_recv_o ; 
        recv_commutes := null_recv_commutes ;
    |} in {| 
        cm_init := morph_init ; 
        cm_recv := morph_recv ;
    |}.

(* TODO: Prove uniqueness *)

End TerminalContract. *)


Section ContractTransformations.
Context {Base : ChainBase}.

(** We define the product of two contracts *)
Section ContractProducts.
Definition init_product 
    { Setup Setup' State State' Error Error' : Type}
    (init  : Chain -> ContractCallContext -> Setup  -> result State  Error)
    (init' : Chain -> ContractCallContext -> Setup' -> result State' Error') :
    (Chain -> ContractCallContext -> Setup * Setup' -> result (State * State') (Error + Error')) := 
    (fun (c : Chain) (ctx : ContractCallContext) (x : Setup * Setup') => 
        match (pair_fun (init c ctx) (init' c ctx) x) with 
        | (Err e, _) => Err (inl e) 
        | (_, Err e) => Err (inr e) 
        | (Ok s, Ok s') => Ok (s, s')
        end).

Definition recv_product 
    { State State' Msg Msg' Error Error' : Type}
    (recv  : Chain -> ContractCallContext -> State  -> option Msg  -> result (State  * list ActionBody) Error)
    (recv' : Chain -> ContractCallContext -> State' -> option Msg' -> result (State' * list ActionBody) Error') : 
    Chain -> ContractCallContext -> State * State' -> option (Msg * Msg') -> result ((State * State') * list ActionBody) (Error + Error') := 
    (fun (c : Chain) (ctx : ContractCallContext) (x1 : State * State') (x2 : option (Msg * Msg')) =>
        let x2' := 
            match x2 with 
            | None => (None, None)
            | Some (x,y) => (Some x, Some y)
            end in 
        match (pair_fun2 (recv c ctx) (recv' c ctx) x1 x2') with 
        | (Err e, _) => Err (inl e)
        | (_, Err e) => Err (inr e) 
        | (Ok r, Ok r') =>
            let (st, actns) := r in 
            let (st', actns') := r' in 
            Ok ((st, st'), actns ++ actns')
        end).

Definition product_contract 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C  : Contract Setup  Msg  State  Error) 
    (C' : Contract Setup' Msg' State' Error') : 
    Contract (Setup * Setup') (Msg * Msg') (State * State') (Error + Error') := 
    build_contract 
        (init_product C.(init) C'.(init))
        (recv_product C.(receive) C'.(receive)).

Lemma product_contract_associative
    { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    `{Serializable Msg''} `{Serializable Setup''} `{Serializable State''} `{Serializable Error''}
    { C : Contract Setup Msg State Error } 
    { C' : Contract Setup' Msg' State' Error' }
    { C'' : Contract Setup'' Msg'' State'' Error'' } : 
    contracts_isomorphic
        (product_contract C (product_contract C' C''))  
        (product_contract (product_contract C C') C'').
Admitted.

End ContractProducts.

(** We define the disjoint sum of two contracts *)
Section ContractSums.
Context { Setup Setup' State State' Error Error' Msg Msg' : Type}
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}.

Definition init_sum 
    (init  : Chain -> ContractCallContext -> Setup  -> result State Error)
    (init' : Chain -> ContractCallContext -> Setup' -> result State' Error') : 
    (Chain -> ContractCallContext -> Setup + Setup' -> result (State + State') (Error + Error' + unit)) := 
    (fun (c : Chain) (ctx : ContractCallContext) (x : Setup + Setup') => 
        match x with 
        | inl s => 
            match init c ctx s with 
            | Ok s' => Ok (inl s')
            | Err e => Err (inl (inl e)) 
            end
        | inr s =>
            match init' c ctx s with 
            | Ok s' => Ok (inr s')
            | Err e => Err (inl (inr e))
            end
        end).

Definition recv_sum 
    (recv  : Chain -> ContractCallContext -> State  -> option Msg  -> result (State  * list ActionBody) Error)
    (recv' : Chain -> ContractCallContext -> State' -> option Msg' -> result (State' * list ActionBody) Error') : 
    Chain -> ContractCallContext -> State + State' -> option (Msg + Msg') -> result ((State + State') * list ActionBody) (Error + Error' + unit) :=
    (fun (c : Chain) (ctx : ContractCallContext) (st : State + State') (op_msg : option (Msg + Msg')) => 
        match st with 
        | inl s => 
            match op_msg with 
            | Some msg => 
                match msg with 
                | inl m => 
                    match recv c ctx s (Some m) with 
                    | Ok (s', actns) => Ok (inl s', actns)
                    | Err e => Err (inl (inl e))
                    end 
                | inr m => Err (inr tt) (* fails if state/msg don't pertain to the same contract *)
                end 
            | None => 
                match recv c ctx s None with 
                | Ok (s', actns) => Ok (inl s', actns)
                | Err e => Err (inl (inl e))
                end 
        end 
        | inr s => 
            match op_msg with 
            | Some msg => 
                match msg with 
                | inr m => 
                    match recv' c ctx s (Some m) with 
                    | Ok (s', actns) => Ok (inr s', actns)
                    | Err e => Err (inl (inr e))
                    end
                | inl m => Err (inr tt) (* fails if state/msg don't pertain to the same contract *)
                end 
            | None => 
                match recv' c ctx s None with 
                | Ok (s', actns) => Ok (inr s', actns)
                | Err e => Err (inl (inr e))
                end
            end 
        end).

(* TODO 
    - Transform actions so addresses are right 
    - Keep track of balances    
*)
Definition sum_contract 
    (C : Contract Setup Msg State Error) 
    (C' : Contract Setup' Msg' State' Error') : 
    Contract (Setup + Setup') (Msg + Msg') (State + State') (Error + Error' + unit) := 
    build_contract 
        (init_sum C.(init) C'.(init))
        (recv_sum C.(receive) C'.(receive)).

End ContractSums.

Section ContractSumsCorrect.
Context { Setup Setup' Setup'' Msg Msg' Msg'' State State' State'' Error Error' Error'' : Type }
    `{Serializable Msg} `{Serializable Setup} `{Serializable State} `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    `{Serializable Msg''} `{Serializable Setup''} `{Serializable State''} `{Serializable Error''}
    { C : Contract Setup Msg State Error } 
    { C' : Contract Setup' Msg' State' Error' }
    { C'' : Contract Setup'' Msg'' State'' Error'' }.

Lemma sum_contract_associative : contracts_isomorphic
        (sum_contract C (sum_contract C' C'')) 
        (sum_contract (sum_contract C C') C'').
Proof. Admitted.

(*
Theorem sum_contract_projects_left : 
    exists (f : ContractMorphism (sum_contract C C') (sum_contract C null_contract)),
        is_surj_cm f.
Proof. Admitted. 

Theorem sum_contract_projects_right : 
    exists (f : ContractMorphism (sum_contract C C') (sum_contract null_contract C')),
        is_surj_cm f.
Proof. Admitted.
*)
Theorem sum_contract_embeds_left : 
    exists (f : ContractMorphism C (sum_contract C C')),
        is_inj_cm f.
Proof. Admitted.

Theorem sum_contract_embeds_right : 
    exists (f : ContractMorphism (sum_contract C C') C'),
        is_inj_cm f.
Proof. Admitted.

(* you want the universal properties, right? *)




(* sum a system of contracts *)



End ContractSumsCorrect.




(** We define the joined sum of two contracts, which will be useful for reasoning about 
    systems of contracts *)
Section JoinedContractSum.

Definition init_joined_sum 
    { Setup Setup' State State' Error Error' : Type}
    (init  : Chain -> ContractCallContext -> Setup  -> result State Error)
    (init' : Chain -> ContractCallContext -> Setup' -> result State' Error') : 
    (Chain -> ContractCallContext -> Setup * Setup' -> result (State * State') (Error + Error')) := 
    (fun (c : Chain) (ctx : ContractCallContext) (x : Setup * Setup') => 
        let (s, s') := x in 
        match init c ctx s with
        | Ok st => 
            match init' c ctx s' with 
            | Ok st' => Ok (st, st')
            | Err e' => Err (inr e')
            end
        | Err e => Err (inl e)
        end).

Definition recv_joined_sum 
    { Msg Msg' State State' Error Error' : Type }
    (recv  : Chain -> ContractCallContext -> State  -> option Msg  -> result (State  * list ActionBody) Error)
    (recv' : Chain -> ContractCallContext -> State' -> option Msg' -> result (State' * list ActionBody) Error') : 
    Chain -> ContractCallContext -> State * State' -> option (Msg + Msg') -> result ((State * State') * list ActionBody) (Error + Error') :=
    (fun (c : Chain) (ctx : ContractCallContext) (st_pair : State * State') (op_msg : option (Msg + Msg')) => 
        let (st, st') := st_pair in 
        match op_msg with 
        | Some msg => 
            match msg with 
            | inl m => 
                match recv c ctx st (Some m) with 
                | Ok rslt => 
                    let (new_st, actns) := rslt in 
                    Ok ((new_st, st'), actns)
                | Err e => Err (inl e) 
                end 
            | inr m => 
                match recv' c ctx st' (Some m) with 
                | Ok rslt => 
                    let (new_st', actns) := rslt in 
                    Ok ((st, new_st'), actns)
                | Err e' => Err (inr e') 
                end 
            end 
        | None => (* is this what you want? *)
            match recv c ctx st None with 
            | Ok rslt => 
                match recv' c ctx st' None with 
                | Ok rslt' => 
                    let (new_st, actns) := rslt in 
                    let (new_st', actns') := rslt' in 
                    Ok ((new_st, new_st'), actns ++ actns')
                | Err e' => Err (inr e') 
                end 
            | Err e => Err (inl e) 
            end 
        end).

Definition joined_sum_contract 
    { Setup Setup' Msg Msg' State State' Error Error' : Type }
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}
    `{Serializable Msg'} `{Serializable Setup'} `{Serializable State'} `{Serializable Error'}
    (C : Contract Setup Msg State Error) 
    (C' : Contract Setup' Msg' State' Error') : 
    Contract (Setup * Setup') (Msg + Msg') (State * State') (Error + Error') := 
    build_contract 
        (init_joined_sum C.(init) C'.(init))
        (recv_joined_sum C.(receive) C'.(receive)).

End JoinedContractSum.


(** Extend the contract's type so it can be the recipient of a morphism. *)
Section PointedContract.
Context { Setup State Error Msg : Type}
    `{Serializable Msg}  `{Serializable Setup}  `{Serializable State}  `{Serializable Error}.

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

(* NEXT : CONSTRUCT BISIMULATIONS OF CHAINS VIA THESE TRANSFORMATIONS
    YOU ONLY NEED TO DO TWO AT A TIME *)


End ContractTransformations.




