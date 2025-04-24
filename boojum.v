(* Require necessary libraries for Vectors and Tactics *)
Require Import Arith. (* Provides arithmetic theorems and tactics *)
Require Import Vector. (* Provides definitions and theorems for fixed-size vectors *)
Require Import Lia.   (* Provides tactics for linear integer/natural number arithmetic *)
Require Import Nat.   (* Provides definitions and theorems for natural numbers (used for Nat.eqb) *)

(* ========================================================================== *)
(* Section 1: Original Boojum Scheme                                          *)
(* ========================================================================== *)
Section BoojumScheme.

  (* -------------------------------------------------------------------------- *)
  (* Parameters and Types                                                       *)
  (* -------------------------------------------------------------------------- *)

  (* Parameter B: Type. (* Represents the type of a byte, e.g., Fin 256 *) *)
  (* We abstract over the concrete type of keys/blocks (e.g., 32 bytes). *)
  Parameter Key : Type. (* Represents B^32, the type of keys and states *)

  (* Parameter for the zero element (e.g., a vector of 32 zero bytes). *)
  Parameter zero_key : Key.

  (* Parameter for the binary XOR operation on Keys (B^32 x B^32 -> B^32). *)
  Parameter xor_op : Key -> Key -> Key.
  (* Define an infix notation for XOR for readability. *)
  Infix "⊕" := xor_op (at level 50, left associativity).

  (* -------------------------------------------------------------------------- *)
  (* Axioms (Assumed Properties)                                                *)
  (* -------------------------------------------------------------------------- *)

  (* Assume the necessary algebraic properties of the XOR operation. *)
  (* In a concrete implementation, these would be proved theorems. *)

  Axiom xor_comm : forall (a b : Key), a ⊕ b = b ⊕ a. (* Commutativity: a ^ b = b ^ a *)
  Axiom xor_assoc : forall (a b c : Key), a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c. (* Associativity: a ^ (b ^ c) = (a ^ b) ^ c *)
  Axiom xor_cancel : forall (a : Key), a ⊕ a = zero_key. (* Cancellation: a ^ a = 0 *)
  Axiom xor_identity : forall (a : Key), a ⊕ zero_key = a. (* Right Identity: a ^ 0 = a *)

  (* Parameter for the cryptographically-secure hash function (e.g., SHA-256). *)
  (* Maps a Key (state) to another Key (hash). *)
  Parameter h_orig : Key -> Key. (* Renamed to avoid clash with the partitioned scheme *)

  (* Parameter for the secret key we want to protect. *)
  Parameter k : Key.

  (* Parameter for the sequence of random keys/bytes from a CSPRNG. *)
  (* R n represents the random value R_n used at step n. *)
  Parameter R_orig : nat -> Key. (* Renamed *)

  (* -------------------------------------------------------------------------- *)
  (* State Definitions (Recursive)                                              *)
  (* -------------------------------------------------------------------------- *)

  (* Define the sequence x_n recursively. *)
  Fixpoint x (n : nat) : Key :=
    match n with
    | 0 => zero_key (* Define x_0 arbitrarily; not used in the theorem (n > 0). *)
    | 1 => R_orig 1      (* Base case: x_1 = R_1 *)
    | S n' => (* Case for n = n' + 1 >= 2 *)
        (* Check if n' is 0 (i.e., if n = 1). This check is slightly redundant *)
        (* due to the previous pattern but ensures safety. *)
        if Nat.eqb n' 0 then R_orig 1
        (* Recursive case: x_{n'+1} = x_{n'} ⊕ R_{n'+1} *)
        else (x n') ⊕ (R_orig (S n'))
    end.

  (* Define the sequence y_n recursively. *)
  Fixpoint y (n : nat) {struct n} : Key :=
     match n with
     | 0 => zero_key (* Define y_0 arbitrarily; not used in the theorem (n > 0). *)
     | 1 => (h_orig (x 1)) ⊕ k (* Base case: y_1 = h(x_1) ⊕ k *)
     | S n' => (* Case for n = n' + 1 >= 2 *)
         if Nat.eqb n' 0 then (h_orig (x 1)) ⊕ k (* Handle n=1 case. *)
         (* Recursive case: y_{n'+1} = y_{n'} ⊕ h(x_{n'}) ⊕ h(x_{n'+1}) *)
         else (y n') ⊕ (h_orig (x n')) ⊕ (h_orig (x (S n')))
     end.

  (* -------------------------------------------------------------------------- *)
  (* Main Theorem and Proof                                                     *)
  (* -------------------------------------------------------------------------- *)

  (* The theorem states the invariant property: k = h(x_n) ⊕ y_n for all n > 0. *)
  (* This demonstrates the "soundness" or correctness of the key recovery mechanism. *)
  (* It proves that, based on the definitions of x and y and the XOR properties, *)
  (* the original key k can always be recovered by computing h(x n) ⊕ y n for any n > 0. *)
  (* This does not prove cryptographic security, which depends on the assumed properties *)
  (* of h_orig and R_orig, but it verifies the mathematical integrity of the scheme's derivation. *)
  Theorem key_invariant : forall (n : nat),
    n > 0 -> k = (h_orig (x n)) ⊕ (y n).
  Proof.
    (* We proceed by induction on n. *)
    intros n Hn. (* Introduce n and the hypothesis n > 0 *)
    induction n as [| n' IH]. (* Induction on n. Base case n=0, inductive step n=S n' *)
    - (* Base case n = 0: *)
      (* The hypothesis Hn is 0 > 0, which is false. *)
      lia. (* lia tactic solves goals involving linear arithmetic contradictions. *)
    - (* Inductive step: Assume property holds for n', prove for n = S n'. *)
      (* IH: n' > 0 -> k = h_orig (x n') ⊕ y n' *)
      (* Goal: S n' > 0 -> k = h_orig (x (S n')) ⊕ y (S n') *)
      (* We need a case split because definitions handle n=1 specially. *)
      destruct n' as [| n''] eqn:Nn'. (* Case split on n': n'=0 or n'=S n'' *)
      + (* Case n = 1 (n' = 0): *)
        simpl. (* Simplify definitions of x and y for n=1. Goal: k = h_orig (R_orig 1) ⊕ (h_orig (x 1) ⊕ k) *)
        (* Apply XOR properties to prove the goal *)
        rewrite -> xor_assoc.   (* k = (h_orig (x 1) ⊕ h_orig (x 1)) ⊕ k *)
        rewrite -> xor_cancel.  (* k = zero_key ⊕ k *)
        rewrite -> xor_comm.    (* k = k ⊕ zero_key *)
        rewrite -> xor_identity. (* k = k *)
        reflexivity. (* Goal is k = k, which is true by reflexivity. *)
      + (* Case n = S n'' >= 2 (n' = S n'' >= 1): *)
        (* We have the inductive hypothesis for n' = S n'' *)
        assert (Hgt0 : S n'' > 0) by lia. (* Prove S n'' > 0 *)
        specialize (IH Hgt0). (* Apply the hypothesis IH: k = h_orig (x (S n'')) ⊕ y (S n'') *)
        simpl. (* Simplify definitions of x and y for n = S(S n'') *)
        (* Goal: k = h_orig(x_{n+1}) ⊕ (y_n ⊕ h_orig(x_n) ⊕ h_orig(x_{n+1})) where n = S n'' *)
        (* Apply XOR properties to simplify the right side to match IH *)
        rewrite (xor_comm (h_orig (x (S (S n''))))). (* Commute h(x_{n+1}) *)
        rewrite <- xor_assoc. (* Re-associate *)
        rewrite xor_cancel.   (* Cancel h(x_{n+1}) ⊕ h(x_{n+1}) *)
        rewrite xor_identity. (* Simplify y_n ⊕ h(x_n) ⊕ zero_key *)
        rewrite xor_comm.     (* Commute to match IH: k = h(x_n) ⊕ y_n *)
        exact IH. (* The goal now exactly matches the inductive hypothesis. *)
  Qed.

End BoojumScheme.

(* ========================================================================== *)
(* Section 2: Extended Boojum Scheme                                          *)
(* ========================================================================== *)
Section ExtendedBoojumScheme.

  (* -------------------------------------------------------------------------- *)
  (* Parameters and Types (using Context for shared parameters)                 *)
  (* -------------------------------------------------------------------------- *)

  (* Assume the same Key type and XOR properties from the previous section *)
  Context {Key : Type}.
  Context {zero_key : Key}.
  Context {xor_op : Key -> Key -> Key}.
  Notation "a ⊕ b" := (xor_op a b) (at level 50, left associativity).
  Context {xor_comm : forall (a b : Key), a ⊕ b = b ⊕ a}.
  Context {xor_assoc : forall (a b c : Key), a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c}.
  Context {xor_cancel : forall (a : Key), a ⊕ a = zero_key}.
  Context {xor_identity : forall (a : Key), a ⊕ zero_key = a}. (* Right identity *)

  (* New Parameters for the Extended Boojum Scheme  *)
  Context {N : nat}. (* Number of partitions. *)
  (* Define Index type for partition index i, where 0 <= i < N. *)
  (* This uses a dependent type: a natural number i along with a proof that i < N. *)
  Definition Index : Type := { i : nat | is_true (Nat.ltb i N) }.

  Context {h : Key -> Key}. (* The hash function used in this scheme (H_{n,i}). *)
  Context {M : Index -> Key}. (* The partitioned secret message M_i. *)
  Context {R : nat -> Index -> Key}. (* Partitioned random bytes R_{n,i}. *)

  (* -------------------------------------------------------------------------- *)
  (* Helper Lemma                                                               *)
  (* -------------------------------------------------------------------------- *)

  (* Helper Lemma: Prove zero_key is also the left identity for XOR. *)
  Lemma xor_identity_left : forall (a : Key), zero_key ⊕ a = a.
  Proof.
    intros a.
    rewrite xor_comm. (* Rewrite zero_key ⊕ a to a ⊕ zero_key *)
    apply xor_identity. (* Apply the right identity axiom: a ⊕ zero_key = a *)
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* State Definitions (Recursive)                                              *)
  (* -------------------------------------------------------------------------- *)

  (* Define the sequence O_{n,i} recursively for each partition i. *)
  (* Note: H_{n,i} in the problem description is interpreted as h(O(n,i)). *)
  Fixpoint O (n : nat) (i : Index) : Key :=
    match n with
    | 0 => zero_key (* Define O(0, i) arbitrarily; not used. *)
    | 1 => R 1 i     (* Base case: O_{1,i} = R_{1,i} *)
    | S n' => (* Case for n = n' + 1 >= 2 *)
        if Nat.eqb n' 0 then R 1 i (* Handle n=1 case. *)
        (* Recursive case: O_{n'+1, i} = O_{n', i} ⊕ R_{n'+1, i} *)
        (* Assuming R_{n+1,i} (i.e., R (S n') i) is used here based on formula structure *)
        else (O n' i) ⊕ (R (S n') i)
    end.

  (* Define the sequence P_{n,i} recursively for each partition i. *)
  Fixpoint P (n : nat) (i : Index) {struct n} : Key :=
     match n with
     | 0 => zero_key (* Define P(0, i) arbitrarily; not used. *)
     | 1 => (h (O 1 i)) ⊕ (M i) (* Base case: P_{1,i} = h(O_{1,i}) ⊕ M_i *)
     | S n' => (* Case for n = n' + 1 >= 2 *)
         if Nat.eqb n' 0 then (h (O 1 i)) ⊕ (M i) (* Handle n=1 case. *)
         (* Recursive case: P_{n'+1, i} = P_{n', i} ⊕ h(O_{n',i}) ⊕ h(O_{n'+1,i}) *)
         else (P n' i) ⊕ (h (O n' i)) ⊕ (h (O (S n') i))
     end.

  (* -------------------------------------------------------------------------- *)
  (* Main Theorem and Proof (Partitioned Scheme)                                *)
  (* -------------------------------------------------------------------------- *)

  (* The theorem states the invariant property for each partition i: M_i = P_{n,i} ⊕ h(O_{n,i}). *)
  (* This proves the soundness (correctness) of the recovery formula for the partitioned scheme. *)
  Theorem partitioned_key_invariant : forall (n : nat) (i : Index),
    n > 0 -> M i = (P n i) ⊕ (h (O n i)).
  Proof.
    (* Proof is by induction on n, similar to the first theorem. *)
    intros n i Hn. (* Introduce n, partition index i, and hypothesis n > 0 *)
    induction n as [| n' IH].
    - (* Base case n = 0: *) lia. (* Contradiction with Hn : 0 > 0 *)
    - (* Inductive step: Assume holds for n', prove for S n'. *)
      (* IH: n' > 0 -> M i = P n' i ⊕ h (O n' i) *)
      (* Goal: S n' > 0 -> M i = P (S n') i ⊕ h (O (S n') i) *)
      destruct n' as [| n''] eqn:Nn'. (* Case split on n': n'=0 or n'=S n'' *)
      + (* Case n = 1 (n' = 0): *)
        simpl. (* Simplify definitions of O and P for n=1. *)
        (* Goal: M i = P 1 i ⊕ h (O 1 i) *)
        (* By definition P 1 i = h (O 1 i) ⊕ M i *)
        (* Goal: M i = (h (O 1 i) ⊕ M i) ⊕ h (O 1 i) *)
        (* Apply XOR properties *)
        rewrite <- xor_assoc.  (* M i = h (O 1 i) ⊕ (M i ⊕ h (O 1 i)) *)
        rewrite xor_comm.      (* M i = h (O 1 i) ⊕ (h (O 1 i) ⊕ M i) *)
        rewrite <- xor_assoc.  (* M i = (h (O 1 i) ⊕ h (O 1 i)) ⊕ M i *)
        rewrite xor_cancel.    (* M i = zero_key ⊕ M i *)
        rewrite xor_identity. (* Use the helper lemma: M i = M i *)
        reflexivity. (* Goal is M i = M i *)
      + (* Case n = S n'' >= 2 (n' = S n'' >= 1): *)
        (* We have the inductive hypothesis for n' = S n'' *)
        assert (Hgt0 : S n'' > 0) by lia.
        specialize (IH Hgt0). (* Apply IH: M i = P (S n'') i ⊕ h (O (S n'') i) *)
        simpl. (* Simplify definitions of O and P for n = S(S n'') *)
        (* Let n denote S n'' and n+1 denote S(S n'') *)
        (* Goal: M i = P (n+1) i ⊕ h (O (n+1) i) *)
        (* Goal: M i = (P n i ⊕ h (O n i) ⊕ h (O (n+1) i)) ⊕ h (O (n+1) i) *)
        (* Apply XOR properties to simplify the right side to match IH *)
        (* Let A = P n i, B = h(O n i), C = h(O (n+1) i) *)
        (* Goal: M i = (A ⊕ B ⊕ C) ⊕ C *)
        rewrite <- xor_assoc. (* M i = A ⊕ (B ⊕ (C ⊕ C)) *) (* Corrected application *)
        rewrite -> xor_cancel. (* M i = A ⊕ (B ⊕ zero_key) *)
        rewrite -> xor_identity. (* M i = A ⊕ B *)
        (* The goal is now M i = P (S n'') i ⊕ h (O (S n'') i), which matches IH *)
        exact IH.
  Qed.

End ExtendedBoojumScheme.

(* Example of using the theorems *)
(* To use these, you would need to provide concrete implementations *)
(* for Key, zero_key, xor_op, h_orig/h, k/M, R_orig/R, N and prove the axioms. *)

(* Check BoojumScheme.key_invariant. *)
(* Check ExtendedBoojumScheme.partitioned_key_invariant. *)