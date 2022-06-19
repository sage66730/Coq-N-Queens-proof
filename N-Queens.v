(** NOTE ################################################################# 

ChessType: nat -> nat
The Constructer patterns described in proposal.
Given a (row: nat) return the (colunm: nat) Queen should be put on.

QueenSolution: nat -> ChessType -> Prop
Check if the given ChessType on a N size board satisfies:
1. queens do not attack vertically (left part)
2. queens do not attack diagonally (right part) 

FianlChess: nat -> ChessType
Decide which ChessType is applied according to board size N.
if N   = |6k+2:     ChessMethod2 N.
         |6k, 6k+4: ChessMethod1 N.
if N-1 = |6k+2:     ChessMethod2 (N-1) and put an additional queen at bottom right corner.
         |6k, 6k+4: ChessMethod1 (N-1) and put an additional queen at bottom right corner.

Problem Reduce (sub-goals):
-Method1:
 1. (V) 2i != 2j
 2. (V) 2i != 2j-N-1
 3. (V) same above
 4. (V) 2i-N-1 != 2j-N-1
 D1.(V) i-j != 2i-2j and i-j != 2j-2i
 D2.(V) i-j != 2i-2j+N+1 and i-j != 2j-N-1-2i #have to use N=6k or 6k=4
 D3.(V) same above
 D4.(V) i-j != 2i-2j and i-j != 2j-2i
-Method2:
 1~16.
 D1~16.
 same concept as method1.

####################################################################### *)
Require Import Arith.
Require Import Lia.

(*
Fixpoint even n : bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
  end.
 *)

Definition ChessType (N: nat):= nat -> nat.
Check ChessType. 

Definition ChessMethod1 (N: nat): ChessType N :=
 fun (i: nat) => if (i <=? N / 2) then (2 * i) else (2 * (i - N / 2) - 1).
 
Definition ChessMethod2 (N: nat): ChessType N :=
  fun (i: nat) => if (i <=? N / 2) then
                    if (2 * i + 1<=? N / 2 + 3) then (2 * i + N / 2 - 2)
                    else                             (2 * i - N / 2 - 2)
                  else
                    if (2 * i <=? 3 * N / 2 - 1 ) then (2 * i - N / 2 + 1)
                    else                               (2 * i - 3 * N / 2 + 1).        
(*
Definition FinalChess (N : nat) : ChessType N :=
  if (andb (even N) ((N mod 6) =? 2)) then ChessMethod2 N
  else
      if (even N) then ChessMethod1 N
      else 
          if (((N - 1) mod 6) =? 2) then (fun (row: nat) => if (row =? N) then N else ChessMethod2 (N - 1) (row))
          else                           (fun (row: nat) => if (row =? N) then N else ChessMethod1 (N - 1) (row)).

Definition ChessMethod3 (N: nat): ChessType N:=
  fun (i: nat) => N.
*)

Definition DiagonalCheck (X1 Y1 X2 Y2: nat) : Prop :=
  ((Y2 + X1) = (X2 + Y1)) \/ ((Y2 + X2) = (X1 + Y1)).
  (* ((Y2 - Y1) = (X2 - X1)) \/ ((Y2 - Y1) = (X1 - X2)). *)
        
Definition QueensSolution (N: nat) (ct: ChessType N): Prop :=
  forall (i j: nat),
    0<i<=N /\ 0<j<=N ->
    ( i<>j -> (ct i)<>(ct j) ) /\ ( i<>j -> ~DiagonalCheck i (ct i) j (ct j) ).

Definition QueensSolution_expand (N: nat) (n: nat) (ct: ChessType n): Prop :=
  forall (i: nat),
    0<i<N ->
    ( (ct i)<>N ) /\ (~DiagonalCheck i (ct i) N N).

(** Major axioms ####################################################################################################*)

Axiom Nat_sub_add:
  forall (m n: nat),
    m - n + n = m.
  
Axiom Nat_mul_div:
  forall (m n: nat),
    n <> 0 ->
    m / n * n = m.

Axiom Nat_add_sub_assoc:
  forall (n m p: nat),
    n + (m - p) = n + m - p.

Axiom Nat_mul_div_assoc:
  forall (n m p: nat),
    p <> 0 ->
    n * m / p = n * (m / p).

Axiom Nat_add_sub_comm:
  forall (n m p: nat),
    n + m - p = n - p + m.

Axiom Nat_div_distr:
  forall (n m p: nat),
    p <> 0 ->
    (n+m)/p = (n/p)+(m/p).

(** Major lemmas ####################################################################################################*)

Lemma self_leq_mult:
  forall (i j: nat),
    (j > 0) -> (i <= i * j).
Proof.
  intros.
  Search "succ_pred".
  apply Nat.succ_pred_pos in H.
  rewrite <- H.
  Search (_*S _).
  rewrite Nat.mul_succ_r.
  Search (_<=_+_).
  apply le_plus_r.
Qed.

Lemma sym_gt_lt:
  forall (m n p: nat),
    m > n <-> n < m.
Proof.
  split.
  auto.
  auto.
Qed.

Lemma deMorgan2b (A B: Prop): ~A/\~B -> ~(A\/B).
Proof.
  intros NANB AB.
  case AB.
  - intro A1.
    destruct NANB.
    contradiction.
  - intro B1.
    destruct NANB.
    contradiction.
Qed.

Lemma double_to_plus:
  forall (n: nat),
    2 * n = n + n.
Proof.
  intros.
  lia.
Qed.

(** Major theorems ####################################################################################################*)
Theorem QueensFinal_6k:
  forall (k: nat), 
    (6*k)>3 -> QueensSolution (6*k) (ChessMethod1 (6*k)).
Proof.
  unfold QueensSolution.
  intros.
  split.
  {
    (* Column should not attack *)
    unfold ChessMethod1.
    intros.
    destruct (i <=? 6 * k / 2) as []eqn:i_up.
    {
      destruct (j <=? 6 * k / 2) as []eqn:j_up.
      (* case 1 *)
      intros contra.
      rewrite Nat.mul_comm in contra.
      symmetry in contra.
      rewrite Nat.mul_comm in contra.
      apply f_equal with (f := fun t => t / 2) in contra.
      Search (_*_/_).
      rewrite Nat.div_mul in contra.
      symmetry in contra.
      rewrite Nat.div_mul in contra.
      contradiction.
      auto.
      auto.
      (*case 2*)
      intro contra.
      apply f_equal with (f := fun t => t + 1) in contra.
      symmetry in contra.
      rewrite Nat.sub_add in contra.
      symmetry in contra.
      apply odd_even_lem in contra.
      assumption.
      Search (_<=?_).
      apply leb_complete_conv in j_up.
      assert (My_H0: 2 <= 2 * (j - 6 * k / 2)).
      {
        apply self_leq_mult.
        rewrite sym_gt_lt.
        Search "lt_O_minus_lt".
        Search "lt_O".
        lia.
        auto.
      }
      Search "le_trans".
      apply (Nat.le_trans 1 2 (2 * (j - 6 * k / 2))).
      auto.
      assumption.
    }
    {
      destruct (j <=? 6 * k / 2) as []eqn:j_up.
      (* case 3 *)
      intro contra.
      apply f_equal with (f := fun t => t + 1) in contra.
      rewrite Nat.sub_add in contra.
      symmetry in contra.
      apply odd_even_lem in contra.
      assumption.
      apply leb_complete_conv in i_up.
      assert (My_H0: 2 <= 2 * (i - 6 * k / 2)).
      {
        apply self_leq_mult.
        rewrite sym_gt_lt.
        lia.
        auto.
      }
      apply (Nat.le_trans 1 2 (2 * (i - 6 * k / 2))).
      auto.
      assumption.
      (* case 4*)
      intro contra.
      apply f_equal with (f := fun t => t + 1) in contra.
      rewrite Nat.sub_add in contra.
      rewrite Nat.mul_comm in contra.
      symmetry in contra.
      rewrite Nat.sub_add in contra.
      rewrite Nat.mul_comm in contra.
      apply f_equal with (f := fun t => t / 2) in contra.
      rewrite Nat.div_mul in contra.
      symmetry in contra.
      rewrite Nat.div_mul in contra.
      apply f_equal with (f := fun t => t + 6 * k / 2) in contra.
      rewrite Nat.sub_add in contra.
      symmetry in contra.
      rewrite Nat.sub_add in contra.
      symmetry in contra.
      contradiction.
      apply leb_complete_conv in j_up.
      Search (_<_ -> _<=_).
      apply Nat.lt_le_incl in j_up.
      assumption.
      apply leb_complete_conv in i_up.
      apply Nat.lt_le_incl in i_up.
      assumption.
      auto.
      auto.
      apply leb_complete_conv in j_up.
      assert (My_H0: 2 <= 2 * (j - 6 * k / 2)).
      {
        apply self_leq_mult.
        rewrite sym_gt_lt.
        lia.
        auto.
      }
      apply (Nat.le_trans 1 2 (2 * (j - 6 * k / 2))).
      auto.
      assumption.
      apply leb_complete_conv in i_up.
      assert (My_H0: 2 <= 2 * (i - 6 * k / 2)).
      {
        apply self_leq_mult.
        rewrite sym_gt_lt.
        lia.
        auto.
      }
      apply (Nat.le_trans 1 2 (2 * (i - 6 * k / 2))).
      auto.
      assumption.
    }
  }
  {
    (*Dia should not attack*)
    unfold DiagonalCheck.
    unfold ChessMethod1.
    intros.
    destruct (i <=? 6 * k / 2) as []eqn:i_up.
    {
      destruct (j <=? 6 * k / 2) as []eqn:j_up.
      (* case D1 *)
      apply deMorgan2b.
      split.
      {
        rewrite double_to_plus.
        Search (_<>_ -> _<>_).
        apply not_eq_sym.
        rewrite double_to_plus.
        Search (_+(_+_)=_+_+_).
        rewrite Nat.add_assoc.
        intro contra.
        apply f_equal with (f := fun t => t - i) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_comm in contra.
        symmetry in contra.
        rewrite Nat.add_sub in contra.
        apply f_equal with (f := fun t => t - j) in contra.
        rewrite Nat.add_sub in contra.
        symmetry in contra.
        rewrite Nat.add_sub in contra.
        contradiction.
      }
      {
        Search (1 * _ = _).
        rewrite <- (Nat.mul_1_l j) at 2.
        Search "distr".
        rewrite <- Nat.mul_add_distr_r.
        rewrite Nat.mul_comm.
        apply not_eq_sym.
        rewrite <- (Nat.mul_1_l i) at 1.
        rewrite Nat.add_comm.
        rewrite <- Nat.mul_add_distr_r.
        rewrite Nat.mul_comm.
        intros contra.
        apply f_equal with (f := fun t => t / (2 + 1)) in contra.
        rewrite Nat.div_mul in contra.
        symmetry in contra.
        rewrite Nat.div_mul in contra.
        symmetry in contra.
        contradiction.
        lia.
        lia.
      }
      (* case D2 *)
      apply deMorgan2b.
      split.
      {
        intro contra.
        rewrite (double_to_plus i) in contra.
        rewrite Nat.add_assoc in contra.
        apply f_equal with (f := fun t => t - i) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.
        Search (_*_=_*_+_*_).
        rewrite Nat.mul_sub_distr_l in contra.
        apply f_equal with (f := fun t => t + (2*(6*k/2))) in contra.
        rewrite Nat_sub_add in contra.        
        rewrite (Nat.mul_comm 6 k)in contra.
        rewrite (Nat.mul_comm 2 (k*6/2))in contra.
        rewrite double_to_plus in contra.
        rewrite Nat_mul_div in contra.
        apply f_equal with (f := fun t => t - j) in contra.
        rewrite Nat.add_sub in contra.
        replace (j + i + 1 + k * 6 - j) with (i + 1 + k * 6) in contra.
        Search "leb".
        apply leb_complete in i_up.
        apply leb_complete_conv in j_up.
        lia.        
        lia.
        auto.
      }
      {
        intro contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite Nat_add_sub_assoc in contra.
        Search "mul_add_dist".
        rewrite <- (Nat.mul_1_l j) in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        rewrite <- (Nat.mul_1_l i) in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        replace (1+2) with 3 in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.     
        rewrite (Nat.mul_comm 6 k)in contra.
        rewrite (Nat.mul_comm 2 (k*6/2))in contra.
        rewrite Nat_mul_div in contra.        
        apply leb_complete in i_up.
        apply leb_complete_conv in j_up.
        lia.
        auto.
        auto.
      }
    }
    {
      destruct (j <=? 6 * k / 2) as []eqn:j_up.
      (* case D3 *)
      apply deMorgan2b.
      split.
      {
        intro contra.
        rewrite (double_to_plus j) in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat.add_assoc in contra.
        rewrite (Nat.add_comm j (2 * (i - 6 * k / 2) - 1))in contra.
        apply f_equal with (f := fun t => t - j) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        apply f_equal with (f := fun t => t + (2*(6*k/2))) in contra.
        rewrite Nat_sub_add in contra.        
        rewrite (Nat.mul_comm 6 k)in contra.
        rewrite (Nat.mul_comm 2 (k*6/2))in contra.
        rewrite double_to_plus in contra.
        rewrite Nat_mul_div in contra.
        apply f_equal with (f := fun t => t - i) in contra.
        rewrite Nat.add_sub in contra.
        replace (i + j + 1 + k * 6 - i) with (j + 1 + k * 6) in contra.
        apply leb_complete_conv in i_up.
        apply leb_complete in j_up.
        lia.        
        lia.
        auto.
      }
      {
        intro contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite <- (Nat.mul_1_l j) in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        rewrite <- (Nat.mul_1_l i) in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        replace (1+2) with 3 in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.     
        rewrite (Nat.mul_comm 6 k)in contra.
        rewrite (Nat.mul_comm 2 (k*6/2))in contra.
        rewrite Nat_mul_div in contra.        
        apply leb_complete_conv in i_up.
        apply leb_complete in j_up.
        lia.
        auto.
        auto.
      }
      (* case D4 *)
      apply deMorgan2b.
      split.
      {
        intro contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite <- Nat.add_assoc in contra.
        rewrite (Nat.add_comm i 1) in contra.
        rewrite Nat.add_assoc in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_sub_add in contra.
        rewrite double_to_plus in contra.
        rewrite (double_to_plus i) in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + (2*(6*k/2))) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat.add_assoc in contra.
        rewrite (Nat.add_comm j (i+i))in contra.
        apply f_equal with (f := fun t => t - j) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_comm in contra.
        apply f_equal with (f := fun t => t - i) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        symmetry in contra.
        contradiction.
      }
      {
        intro contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite <- Nat.add_assoc in contra.
        rewrite (Nat.add_comm j 1) in contra.
        rewrite Nat.add_assoc in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + (2*(6*k/2))) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_sub_add in contra.
        rewrite <- (Nat.mul_1_l j)in contra at 1.
        rewrite <- (Nat.mul_1_l i)in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        rewrite <- Nat.mul_add_distr_r in contra.
        replace (1+2) with 3 in contra.
        rewrite Nat.mul_comm in contra.
        rewrite (Nat.mul_comm 3 i) in contra.
        apply f_equal with (f := fun t => t / 3) in contra.
        rewrite Nat.div_mul in contra.
        rewrite Nat.div_mul in contra.
        symmetry in contra.
        contradiction.
        auto.
        auto.
        auto.
      }
    }
  }
Qed.


Theorem QueensFinal_6k1:
  forall (k: nat), 
    (6*k+1)>3 ->
    (QueensSolution_expand (6*k+1) (6*k) (ChessMethod1 (6*k))).
Proof.
  unfold QueensSolution_expand.
  unfold ChessMethod1.
  intros.
  split.
  {
    (* Column should not attack *)
    destruct (i <=? 6 * k / 2) as []eqn:i_up.
    {
      (* case up *)
      lia.
    }
    {
      (* case down *)
      intro contra.
      apply leb_complete_conv in i_up.
      apply f_equal with (f := fun t => t + 1) in contra.
      rewrite Nat_sub_add in contra.
      rewrite <- Nat.add_assoc in contra.
      replace (1 + 1) with 2 in contra.
      rewrite Nat.mul_sub_distr_l in contra.
      apply f_equal with (f := fun t => t + (2*(6*k/2))) in contra.
      rewrite Nat_sub_add in contra.
      rewrite (Nat.mul_comm 2 (6*k/2)) in contra.
      rewrite Nat_mul_div in contra.
      lia.
      auto.
      auto.
    }
  }
  {
    (* Dia should not attack *)
    unfold DiagonalCheck.
    apply deMorgan2b.
    destruct (i <=? 6 * k / 2) as []eqn:i_up.
    {
      (* case up *)
      split.
      {
        lia.
      }
      {
        lia.
      }
    }
    {
      (* case down *)
      apply leb_complete_conv in i_up.
      split.
      {
        intros contra.
        rewrite (Nat.add_comm (6*k+1) i) in contra.
        rewrite (Nat.add_comm (6*k+1) (2*(i-6*k/2)-1)) in contra.
        apply f_equal with (f := fun t => t - (6 * k + 1)) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite (Nat.mul_comm 2 (6*k/2)) in contra.
        rewrite Nat_mul_div in contra.
        lia.
        auto.
      }
      {
        intro contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite (Nat.mul_comm 2 (6*k/2)) in contra.
        rewrite Nat_mul_div in contra.
        lia.
        auto.
      }
    }
  }
Qed.

(*
copy~
            apply leb_complete_conv in i_up.
            apply leb_complete_conv in i_next_up.
            apply leb_complete_conv in j_up.
            apply leb_complete_conv in j_next_up.

*)

Theorem QueensFinal_6k2:
  forall (k: nat), 
    (6*k+2)>3 -> QueensSolution (6*k+2) (ChessMethod2 (6*k+2)).
Proof.
  unfold QueensSolution.
  unfold ChessMethod2.
  intros.
  split.
  intros.
  {
    (* Column should not attack *)
    destruct (i <=? (6 * k + 2) / 2) as []eqn:i_up.
    {
      apply leb_complete in i_up.
      destruct (2 * i + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:i_next_up.
      {
        (* i1 *)
        apply leb_complete in i_next_up.
        destruct (j <=? (6 * k + 2) / 2) as []eqn:j_up.
        {
          apply leb_complete in j_up.
          destruct (2 * j + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:j_next_up.
          {
            (* i1 j1 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* i1 j2*)
            apply leb_complete_conv in j_next_up.
            lia.
          }
        }
        {
          apply leb_complete_conv in j_up.
          destruct (2 * j <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:j_next_up.
          {
            (* i1 j3 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* i1 j4 *)
            apply leb_complete_conv in j_next_up.
            intro contra.
            replace ((6 * k + 2) / 2) with (3 * k + 1) in contra.
            replace (3 * (6 * k + 2) / 2) with (3 * (3 * k + 1)) in contra.
            lia.            
            rewrite Nat_mul_div_assoc.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite (Nat_mul_div_assoc k 6 2).
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto. auto.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite Nat_mul_div_assoc.
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto.
          }
        }  
      }
      {
        (* i2 *)
        apply leb_complete_conv in i_next_up.
        destruct (j <=? (6 * k + 2) / 2) as []eqn:j_up.
        {
          apply leb_complete in j_up.
          destruct (2 * j + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:j_next_up.
          {
            (* i2 j1 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* i2 j2*)
            apply leb_complete_conv in j_next_up.
            lia.
          }
        }
        {
          apply leb_complete_conv in j_up.
          destruct (2 * j <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:j_next_up.
          {
            (* i2 j3 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* i2 j4 *)
            apply leb_complete_conv in j_next_up.
            intro contra.
            replace ((6 * k + 2) / 2) with (3 * k + 1) in contra.
            replace (3 * (6 * k + 2) / 2) with (3 * (3 * k + 1)) in contra.
            apply f_equal with (f := fun t => t + 2) in contra.
            rewrite <- (Nat.add_assoc _ 1 2) in contra.
            replace (1+2) with 3 in contra.
            rewrite Nat_sub_add in contra.
            apply f_equal with (f := fun t => t + 3*(3*k+1)) in contra.
            rewrite <- (Nat.add_assoc _ 3 (3*(3*k+1))) in contra.
            rewrite (Nat.add_comm 3 (3*(3*k+1))) in contra.
            rewrite (Nat.add_assoc _ (3*(3*k+1)) 3) in contra.
            rewrite Nat_sub_add in contra.
            replace 3 with (1+2) in contra at 2.
            rewrite Nat.mul_add_distr_r in contra.
            rewrite Nat.mul_1_l in contra.
            rewrite Nat.add_assoc in contra.
            rewrite Nat_sub_add in contra.
            lia.
            auto. auto.
            rewrite Nat_mul_div_assoc.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite (Nat_mul_div_assoc k 6 2).
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto. auto.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite Nat_mul_div_assoc.
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto.
          }
        }
      }
    }
    {
      apply leb_complete_conv in i_up.
      destruct (2 * i <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:i_next_up.
      {
        (* i3 *)
        apply leb_complete in i_next_up.
        destruct (j <=? (6 * k + 2) / 2) as []eqn:j_up.
        {
          apply leb_complete in j_up.
          destruct (2 * j + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:j_next_up.
          {
            (* i3 j1 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* i3 j2*)
            apply leb_complete_conv in j_next_up.
            lia.
          }
        }
        {
          apply leb_complete_conv in j_up.
          destruct (2 * j <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:j_next_up.
          {
            (* i3 j3 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* i3 j4 *)
            apply leb_complete_conv in j_next_up.
            intro contra.
            destruct H0.
            destruct H2.
            rewrite Nat_div_distr in i_up.
            rewrite (Nat.mul_comm 6 k) in i_up.
            rewrite Nat_mul_div_assoc in i_up.
            replace (6/2) with 3 in i_up.
            rewrite Nat.mul_comm in i_up.
            rewrite Nat.div_same in i_up.
            replace ((6 * k + 2) / 2) with (3 * k + 1) in contra.
            replace (3 * (6 * k + 2) / 2) with (3 * (3 * k + 1)) in contra.
            apply f_equal with (f := fun t => t - 1) in contra.
            rewrite Nat.add_sub in contra.
            rewrite Nat.add_sub in contra.
            apply f_equal with (f := fun t => t + 3*(3*k+1)) in contra.
            rewrite Nat_sub_add in contra.
            lia.
            rewrite Nat_mul_div_assoc.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite (Nat_mul_div_assoc k 6 2).
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto. auto.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite Nat_mul_div_assoc.
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto. auto. auto. auto. auto.
          }
        }
      }
      {
        (* i4 *)
        apply leb_complete_conv in i_next_up.
        destruct (j <=? (6 * k + 2) / 2) as []eqn:j_up.
        {
          apply leb_complete in j_up.
          destruct (2 * j + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:j_next_up.
          {
            (* i4 j1 *)
            apply leb_complete in j_next_up.
            intro contra.
            replace ((6 * k + 2) / 2) with (3 * k + 1) in contra.
            replace (3 * (6 * k + 2) / 2) with (3 * (3 * k + 1)) in contra.
            lia.            
            rewrite Nat_mul_div_assoc.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite (Nat_mul_div_assoc k 6 2).
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto. auto.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite Nat_mul_div_assoc.
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto.
          }
          {
            (* i4 j2*)
            apply leb_complete_conv in j_next_up.
            intro contra.
            replace ((6 * k + 2) / 2) with (3 * k + 1) in contra.
            replace (3 * (6 * k + 2) / 2) with (3 * (3 * k + 1)) in contra.
            apply f_equal with (f := fun t => t + 2) in contra.
            rewrite <- (Nat.add_assoc _ 1 2) in contra.
            replace (1+2) with 3 in contra.
            rewrite Nat_sub_add in contra.
            apply f_equal with (f := fun t => t + 3*(3*k+1)) in contra.
            rewrite <- (Nat.add_assoc _ 3 (3*(3*k+1))) in contra.
            rewrite (Nat.add_comm 3 (3*(3*k+1))) in contra.
            rewrite (Nat.add_assoc _ (3*(3*k+1)) 3) in contra.
            rewrite Nat_sub_add in contra.
            replace 3 with (1+2) in contra at 3.
            rewrite Nat.mul_add_distr_r in contra.
            rewrite Nat.mul_1_l in contra.
            rewrite Nat.add_assoc in contra.
            rewrite Nat_sub_add in contra.
            lia.
            auto. auto.
            rewrite Nat_mul_div_assoc.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite (Nat_mul_div_assoc k 6 2).
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto. auto.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite Nat_mul_div_assoc.
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto.
          }
        }
        {
          apply leb_complete_conv in j_up.
          destruct (2 * j <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:j_next_up.
          {
            (* i4 j3 *)
            apply leb_complete in j_next_up.
            intro contra.
            destruct H0.
            destruct H0.
            rewrite Nat_div_distr in j_up.
            rewrite (Nat.mul_comm 6 k) in j_up.
            rewrite Nat_mul_div_assoc in j_up.
            replace (6/2) with 3 in j_up.
            rewrite Nat.mul_comm in j_up.
            rewrite Nat.div_same in j_up.
            replace ((6 * k + 2) / 2) with (3 * k + 1) in contra.
            replace (3 * (6 * k + 2) / 2) with (3 * (3 * k + 1)) in contra.
            apply f_equal with (f := fun t => t - 1) in contra.
            rewrite Nat.add_sub in contra.
            rewrite Nat.add_sub in contra.
            apply f_equal with (f := fun t => t + 3*(3*k+1)) in contra.
            rewrite Nat_sub_add in contra.
            lia.
            rewrite Nat_mul_div_assoc.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite (Nat_mul_div_assoc k 6 2).
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto. auto.
            rewrite Nat_div_distr.
            rewrite (Nat.mul_comm 6 k).
            rewrite Nat_mul_div_assoc.
            replace (6/2) with 3.
            rewrite (Nat.mul_comm k 3).
            replace (2/2) with 1.
            auto. auto. auto. auto. auto. auto. auto. auto. auto.
          }
          {
            (* i4 j4 *)
            apply leb_complete_conv in j_next_up.
            lia.
          }
        }
      }
    }
  }
  {
    (* Dia should not attack *)
    unfold DiagonalCheck.
    intros.
    destruct (i <=? (6 * k + 2) / 2) as []eqn:i_up.
    {
      apply leb_complete in i_up.
      destruct (2 * i + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:i_next_up.
      {
        (* D i1 *)
        apply leb_complete in i_next_up.
        destruct (j <=? (6 * k + 2) / 2) as []eqn:j_up.
        {
          apply leb_complete in j_up.
          destruct (2 * j + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:j_next_up.
          {
            (* D i1 j1 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* D i1 j2*)
            apply leb_complete_conv in j_next_up.
            apply deMorgan2b.
            split.
            - lia.
            - intro contra.
              rewrite Nat.add_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat.add_assoc in contra.
              apply f_equal with (f := fun t => t + 2) in contra.
              rewrite Nat_sub_add in contra.
              rewrite Nat_sub_add in contra.
              apply f_equal with (f := fun t => t + ((6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat.add_assoc in contra.
              rewrite <- double_to_plus in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto.
          }
        }
        {
          apply leb_complete_conv in j_up.
          destruct (2 * j <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:j_next_up.
          {
            (* D i1 j3 *)
            apply leb_complete in j_next_up.
            apply deMorgan2b.
            split.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite (Nat_add_sub_comm j _ 2)in contra.
              rewrite (Nat.add_assoc (j-2) _ _) in contra.
              apply f_equal with (f := fun t => t + ((6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- (Nat.add_assoc (j-2+2*i) _ _)in contra.
              rewrite <- double_to_plus in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              rewrite (Nat.add_comm _ (6*k+2))in contra.
              rewrite Nat.add_assoc in contra.
              apply f_equal with (f := fun t => t - i) in contra.
              rewrite Nat.add_sub in contra.
              rewrite <- (Nat_add_sub_assoc _ _ i)in contra.
              replace (2*i-i) with i in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat_add_sub_comm in contra.
              rewrite Nat.add_sub in contra.
              rewrite Nat.add_comm in contra.
              rewrite <- Nat.add_assoc in contra.
              rewrite (Nat.add_comm j i)in contra.
              rewrite Nat.add_assoc in contra.
              apply f_equal with (f := fun t => t - j) in contra.
              rewrite Nat.add_sub in contra.
              rewrite <- (Nat_add_sub_assoc _ _ j)in contra.
              replace (2*j-j) with j in contra.
              lia.
              lia.
              lia.
              auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite (Nat_add_sub_comm i _ 2)in contra.
              rewrite (Nat.add_assoc (i-2) _ _) in contra.
              apply f_equal with (f := fun t => t + ((6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- (Nat.add_assoc (i-2+2*i) _ _) in contra.
              rewrite <- double_to_plus in contra.
              rewrite <- (Nat.add_assoc _ 1 j) in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2))in contra.
              rewrite Nat_mul_div in contra.
              rewrite (Nat.add_comm 1 j) in contra.
              rewrite (Nat.add_assoc _ j 1) in contra.
              replace (2*j+j) with (3*j) in contra.
              rewrite <- Nat_add_sub_comm in contra.
              replace (i+2*i) with (3*i) in contra.
              lia.
              lia.
              lia.
              auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
          }
          {
            (* D i1 j4 *)
            apply leb_complete_conv in j_next_up.
            apply deMorgan2b.
            split.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite (Nat_add_sub_comm j _ 2)in contra.
              rewrite (Nat.add_assoc (j-2) _ _) in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat.add_assoc (j-2+2*i) _ _) in contra.
              rewrite Nat_mul_div_assoc in contra.
              rewrite <- Nat.mul_add_distr_r in contra.
              replace (1+3) with (2*2) in contra.
              rewrite <- Nat.mul_assoc in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto.
              lia.
              auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite (Nat_add_sub_comm i _ 2)in contra.
              rewrite (Nat.add_assoc (i-2) _ _) in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat.add_assoc (i-2+2*i) _ _) in contra.
              rewrite Nat_mul_div_assoc in contra.
              rewrite <- Nat.mul_add_distr_r in contra.
              replace (1+3) with (2*2) in contra.
              rewrite <- Nat.mul_assoc in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto.
              lia.
              auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
          }
        }  
      }
      {
        (* D i2 *)
        apply leb_complete_conv in i_next_up.
        destruct (j <=? (6 * k + 2) / 2) as []eqn:j_up.
        {
          apply leb_complete in j_up.
          destruct (2 * j + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:j_next_up.
          {
            (* D i2 j1 *)
            apply leb_complete in j_next_up.
            apply deMorgan2b.
            split.
            - lia.
            - intro contra.
              rewrite Nat.add_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat.add_assoc in contra.
              apply f_equal with (f := fun t => t + 2) in contra.
              rewrite Nat_sub_add in contra.
              rewrite Nat_sub_add in contra.
              apply f_equal with (f := fun t => t + ((6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat.add_assoc in contra.
              rewrite <- double_to_plus in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto.
          }
          {
            (* D i2 j2*)
            apply leb_complete_conv in j_next_up.
            lia.
          }
        }
        {
          apply leb_complete_conv in j_up.
          destruct (2 * j <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:j_next_up.
          {
            (* D i2 j3 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* D i2 j4 *)
            apply leb_complete_conv in j_next_up.
            apply deMorgan2b.
            split.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite (Nat_add_sub_comm j _ 2) in contra.
              rewrite (Nat_add_sub_assoc (j-2)_  _) in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat.add_assoc (j-2) _ _) in contra.
              rewrite (Nat_mul_div_assoc 3 _ 2) in contra.
              rewrite (Nat.add_assoc (j-2) _ _) in contra.
              rewrite <- Nat_add_sub_assoc in contra.
              rewrite <- Nat.mul_sub_distr_r in contra.
              replace (3-1) with 2 in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite (Nat_add_sub_comm i _ 2) in contra.
              rewrite (Nat_add_sub_assoc (i-2)_  _) in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat.add_assoc (i-2) _ _) in contra.
              rewrite (Nat_mul_div_assoc 3 _ 2) in contra.
              rewrite (Nat.add_assoc (i-2) _ _) in contra.
              rewrite <- Nat_add_sub_assoc in contra.
              rewrite <- Nat.mul_sub_distr_r in contra.
              replace (3-1) with 2 in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
          }
        }
      }
    }
    {
      apply leb_complete_conv in i_up.
      destruct (2 * i <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:i_next_up.
      {
        (* D i3 *)
        apply leb_complete in i_next_up.
        destruct (j <=? (6 * k + 2) / 2) as []eqn:j_up.
        {
          apply leb_complete in j_up.
          destruct (2 * j + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:j_next_up.
          {
            (* D i3 j1 *)
            apply leb_complete in j_next_up.
            apply deMorgan2b.
            split.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in j_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_comm in contra.
              rewrite <- Nat.add_assoc in contra.
              rewrite (Nat.add_comm _ i) in contra.
              rewrite Nat.add_assoc in contra.
              apply f_equal with (f := fun t => t + ((6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- (Nat.add_assoc (2*j-2+i) _ _)in contra.
              rewrite <- double_to_plus in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in j_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_comm in contra.
              rewrite <- Nat.add_assoc in contra.
              rewrite (Nat.add_comm _ j) in contra.
              rewrite Nat.add_assoc in contra.
              apply f_equal with (f := fun t => t + ((6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- (Nat.add_assoc (2*j-2+j) _ _)in contra.
              rewrite <- double_to_plus in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
          }
          {
            (* D i3 j2*)
            apply leb_complete_conv in j_next_up.
            lia.
          }
        }
        {
          apply leb_complete_conv in j_up.
          destruct (2 * j <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:j_next_up.
          {
            (* D i3 j3 *)
            apply leb_complete in j_next_up.
            lia.
          }
          {
            (* D i3 j4 *)
            apply leb_complete_conv in j_next_up.
            apply deMorgan2b.
            split.
            - intro contra.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.            
              rewrite (Nat_add_sub_assoc j (2*i+1) _)in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat_add_sub_assoc (j+(2*i+1)) _ _) in contra.
              rewrite (Nat_mul_div_assoc 3 _ 2) in contra.
              rewrite <- Nat.mul_sub_distr_r in contra.
              replace (3-1) with 2 in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.              
            - intro contra.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.            
              rewrite (Nat_add_sub_assoc i (2*i+1) _)in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat_add_sub_assoc (i+(2*i+1)) _ _) in contra.
              rewrite (Nat_mul_div_assoc 3 _ 2) in contra.
              rewrite <- Nat.mul_sub_distr_r in contra.
              replace (3-1) with 2 in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto. 
          }
        }
      }
      {
        (* D i4 *)
        apply leb_complete_conv in i_next_up.
        destruct (j <=? (6 * k + 2) / 2) as []eqn:j_up.
        {
          apply leb_complete in j_up.
          destruct (2 * j + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:j_next_up.
          {
            (* D i4 j1 *)
            apply leb_complete in j_next_up.
            apply deMorgan2b.
            split.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in j_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite <- Nat_add_sub_assoc in contra.
              rewrite <- Nat.add_assoc in contra.
              rewrite (Nat.add_comm _ (i-2))in contra.
              rewrite Nat.add_assoc in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat.add_assoc (2*j+(i-2)) _ _) in contra.
              rewrite Nat_mul_div_assoc in contra.
              rewrite <- Nat.mul_add_distr_r in contra.
              replace (1+3) with (2*2) in contra.
              rewrite <- Nat.mul_assoc in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto.
              lia.
              auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in j_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite Nat_add_sub_assoc in contra.
              rewrite <- Nat_add_sub_assoc in contra.
              rewrite <- Nat.add_assoc in contra.
              rewrite (Nat.add_comm _ (j-2))in contra.
              rewrite Nat.add_assoc in contra.              
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat.add_assoc (2*j+(j-2)) _ _) in contra.
              rewrite Nat_mul_div_assoc in contra.
              rewrite <- Nat.mul_add_distr_r in contra.
              replace (1+3) with (2*2) in contra.
              rewrite <- Nat.mul_assoc in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto.
              lia.
              auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
          }
          {
            (* D i4 j2*)
            apply leb_complete_conv in j_next_up.
            apply deMorgan2b.
            split.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in j_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_assoc in contra.
              rewrite <- Nat_add_sub_comm in contra.            
              rewrite (Nat.add_comm _ 1) in contra.
              rewrite Nat.add_assoc in contra.
              rewrite <- (Nat.add_assoc j 1 _)in contra.              
              rewrite (Nat_add_sub_assoc 1 _  _)in contra.
              rewrite (Nat_add_sub_assoc j (1+2*i) _)in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat_add_sub_assoc (2*j+(i-2)) _ _) in contra.
              rewrite (Nat_mul_div_assoc 3 _ 2) in contra.
              rewrite <- Nat.mul_sub_distr_r in contra.
              replace (3-1) with 2 in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
            - intro contra.
              replace ((6*k+2)/2) with (3*k+1) in j_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_assoc in contra.
              rewrite <- Nat_add_sub_comm in contra.            
              rewrite (Nat.add_comm _ 1) in contra.
              rewrite Nat.add_assoc in contra.
              rewrite <- (Nat.add_assoc i 1 _)in contra.              
              rewrite (Nat_add_sub_assoc 1 _  _)in contra.
              rewrite (Nat_add_sub_assoc i (1+2*i) _)in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat_add_sub_assoc (2*j+(j-2)) _ _) in contra.
              rewrite (Nat_mul_div_assoc 3 _ 2) in contra.
              rewrite <- Nat.mul_sub_distr_r in contra.
              replace (3-1) with 2 in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto.
          }
        }
        {
          apply leb_complete_conv in j_up.
          destruct (2 * j <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:j_next_up.
          {
            (* D i4 j3 *)
            apply leb_complete in j_next_up.
            apply deMorgan2b.
            split.
            - intro contra.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.            
              rewrite (Nat_add_sub_assoc j (2*i+1) _)in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat_add_sub_assoc (2*j+1+i) _ _) in contra.
              rewrite (Nat_mul_div_assoc 3 _ 2) in contra.
              rewrite <- Nat.mul_sub_distr_r in contra.
              replace (3-1) with 2 in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.  
            - intro contra.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
              replace (3*(6*k+2)/2) with (3*(3*k+1)) in j_next_up.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- Nat_add_sub_comm in contra.            
              rewrite (Nat_add_sub_assoc i (2*i+1) _)in contra.
              apply f_equal with (f := fun t => t + (3*(6*k+2)/2)) in contra.
              rewrite Nat_sub_add in contra.
              rewrite <- Nat_add_sub_comm in contra.
              rewrite <- (Nat.mul_1_l ((6*k+2)/2)) in contra.
              rewrite <- (Nat_add_sub_assoc (2*j+1+j) _ _) in contra.
              rewrite (Nat_mul_div_assoc 3 _ 2) in contra.
              rewrite <- Nat.mul_sub_distr_r in contra.
              replace (3-1) with 2 in contra.
              rewrite (Nat.mul_comm 2 ((6*k+2)/2)) in contra.
              rewrite Nat_mul_div in contra.
              lia.
              auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto.
              rewrite Nat_mul_div_assoc.
              replace ((6*k+2)/2) with (3*k+1).
              auto.
              rewrite Nat_div_distr.
              rewrite (Nat.mul_comm 6 k).
              rewrite Nat_mul_div_assoc.
              replace (6/2) with 3.
              rewrite (Nat.mul_comm k 3).
              replace (2/2) with 1.
              auto. auto. auto. auto. auto. auto. 
          }
          {
            (* D i4 j4 *)
            apply leb_complete_conv in j_next_up.
            lia.
          }
        }
      }
    }
  }
Qed.

Theorem QueensFinal_6k3:
  forall (k: nat), 
    (6*k+3)>3 ->
    (QueensSolution_expand (6*k+3) (6*k+2) (ChessMethod2 (6*k+2))).
Proof.
  unfold QueensSolution.
  unfold ChessMethod2.
  intros.
  split.
  {
    (* Column should not attack *)
    intros.
    destruct (i <=? (6 * k + 2) / 2) as []eqn:i_up.
    {
      apply leb_complete in i_up.
      destruct (2 * i + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:i_next_up.
      {
        (* i1 *)
        apply leb_complete in i_next_up.
        intro contra.
        replace ((6*k+2)/2) with (3*k+1) in i_next_up.        
        replace ((6*k+2)/2) with (3*k+1) in contra.
        apply f_equal with (f := fun t => t + 2) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat.add_assoc in contra.
        rewrite <- (Nat.add_assoc _ 3 2) in contra.
        replace (3+2) with 5 in contra.
        apply f_equal with (f := fun t => t - 1) in contra.
        rewrite Nat.add_sub in contra.
        rewrite <- Nat.add_sub_assoc in contra.
        replace (5-1) with 4 in contra.
        lia.
        auto. auto. auto.
        rewrite Nat_div_distr.
        rewrite (Nat.mul_comm 6 k).
        rewrite Nat_mul_div_assoc.
        replace (6/2) with 3.
        rewrite (Nat.mul_comm k 3).
        replace (2/2) with 1.
        auto. auto. auto. auto. auto.
        rewrite Nat_div_distr.
        rewrite (Nat.mul_comm 6 k).
        rewrite Nat_mul_div_assoc.
        replace (6/2) with 3.
        rewrite (Nat.mul_comm k 3).
        replace (2/2) with 1.
        auto. auto. auto. auto. auto.
      }
      {
        (* i2 *)
        apply leb_complete_conv in i_next_up.
        lia.
      }
    }
    {
      apply leb_complete_conv in i_up.
      destruct (2 * i <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:i_next_up.
      {
        (* i3 *)
        apply leb_complete in i_next_up.
        intro contra.
        replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.        
        replace ((6*k+2)/2) with (3*k+1) in contra.
        apply f_equal with (f := fun t => t - 1) in contra.
        rewrite Nat.add_sub in contra.
        rewrite <- Nat_add_sub_assoc in contra.
        replace (3-1) with 2 in contra.
        apply f_equal with (f := fun t => t + (3*k+1)) in contra.
        rewrite Nat_sub_add in contra.
        lia.
        auto.
        rewrite Nat_div_distr.
        rewrite (Nat.mul_comm 6 k).
        rewrite Nat_mul_div_assoc.
        replace (6/2) with 3.
        rewrite (Nat.mul_comm k 3).
        replace (2/2) with 1.
        auto. auto. auto. auto. auto.
        rewrite Nat_mul_div_assoc.
        replace ((6*k+2)/2) with (3*k+1).
        auto.
        rewrite Nat_div_distr.
        rewrite (Nat.mul_comm 6 k).
        rewrite Nat_mul_div_assoc.
        replace (6/2) with 3.
        rewrite (Nat.mul_comm k 3).
        replace (2/2) with 1.
        auto. auto. auto. auto. auto.
        auto.
      }
      {
        (* i4 *)
        apply leb_complete_conv in i_next_up.
        intro contra.
        replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
        replace (3*(6*k+2)/2) with (3*(3*k+1)) in contra.        
        lia.
        rewrite Nat_mul_div_assoc.
        replace ((6*k+2)/2) with (3*k+1).
        auto.
        rewrite Nat_div_distr.
        rewrite (Nat.mul_comm 6 k).
        rewrite Nat_mul_div_assoc.
        replace (6/2) with 3.
        rewrite (Nat.mul_comm k 3).
        replace (2/2) with 1.
        auto. auto. auto. auto. auto. auto.
        rewrite Nat_mul_div_assoc.
        replace ((6*k+2)/2) with (3*k+1).
        auto.
        rewrite Nat_div_distr.
        rewrite (Nat.mul_comm 6 k).
        rewrite Nat_mul_div_assoc.
        replace (6/2) with 3.
        rewrite (Nat.mul_comm k 3).
        replace (2/2) with 1.
        auto. auto. auto. auto. auto. auto.
      }
    }
  }
  {
    (* Dia should not attack *)
    intros.
    unfold DiagonalCheck.
    destruct (i <=? (6 * k + 2) / 2) as []eqn:i_up.
    {
      apply leb_complete in i_up.
      destruct (2 * i + 1 <=? (6 * k + 2) / 2 + 3) as []eqn:i_next_up.
      {
        (* D i1 *)
        apply leb_complete in i_next_up.
        replace ((6*k+2)/2) with (3*k+1) in i_next_up.
        apply deMorgan2b.
        split.
        - intro contra.
          replace ((6*k+2)/2) with (3*k+1) in contra.
          lia.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto.
        - intro contra.
          replace ((6*k+2)/2) with (3*k+1) in contra.
          lia.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto.
        - rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto.
      }
      {
        (* D i2 *)
        apply leb_complete_conv in i_next_up.
        lia.
      }
    }
    {
      apply leb_complete_conv in i_up.
      destruct (2 * i <=? 3 * (6 * k + 2) / 2 - 1) as []eqn:i_next_up.
      {
        (* D i3 *)
        apply leb_complete in i_next_up.
        replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
        apply deMorgan2b.
        split.
        - intro contra.
          replace ((6*k+2)/2) with (3*k+1) in i_up.
          replace ((6*k+2)/2) with (3*k+1) in contra.  
          lia.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto. auto.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto.
        - intro contra.
          replace ((6*k+2)/2) with (3*k+1) in i_up.
          replace ((6*k+2)/2) with (3*k+1) in contra.
          lia.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto. auto.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto.
        - rewrite Nat_mul_div_assoc.
          replace ((6*k+2)/2) with (3*k+1).
          auto.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto. auto.
      }
      {
        apply leb_complete_conv in i_next_up.
        (* D i4 *)
        replace (3*(6*k+2)/2) with (3*(3*k+1)) in i_next_up.
        apply deMorgan2b.
        split.
        - intro contra.
          replace ((6*k+2)/2) with (3*k+1) in i_up.
          replace (3*(6*k+2)/2) with (3*(3*k+1)) in contra.
          lia.
          rewrite Nat_mul_div_assoc.
          replace ((6*k+2)/2) with (3*k+1).
          auto.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto. auto.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto.
        - intro contra.
          replace ((6*k+2)/2) with (3*k+1) in i_up.
          replace (3*(6*k+2)/2) with (3*(3*k+1)) in contra.
          lia.
          rewrite Nat_mul_div_assoc.
          replace ((6*k+2)/2) with (3*k+1).
          auto.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto. auto.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto.
        - rewrite Nat_mul_div_assoc.
          replace ((6*k+2)/2) with (3*k+1).
          auto.
          rewrite Nat_div_distr.
          rewrite (Nat.mul_comm 6 k).
          rewrite Nat_mul_div_assoc.
          replace (6/2) with 3.
          rewrite (Nat.mul_comm k 3).
          replace (2/2) with 1.
          auto. auto. auto. auto. auto. auto.
      }
    }
  }
Qed.

Theorem QueensFinal_6k4:
  forall (k: nat), 
     (QueensSolution (6*k+4) (ChessMethod1 (6*k+4))).
Proof.
  unfold QueensSolution.
  intros.
  split.
  {
    (* Column should not attack *)
    unfold ChessMethod1.
    intros.
    destruct (i <=? (6 * k + 4) / 2) as []eqn:i_up.
    {
      destruct (j <=? (6 * k + 4) / 2) as []eqn:j_up.
      (* case 1 *)
      intros contra.
      rewrite Nat.mul_comm in contra.
      symmetry in contra.
      rewrite Nat.mul_comm in contra.
      apply f_equal with (f := fun t => t / 2) in contra.
      rewrite Nat.div_mul in contra.
      symmetry in contra.
      rewrite Nat.div_mul in contra.
      contradiction.
      auto.
      auto.
      (*case 2*)
      intro contra.
      apply f_equal with (f := fun t => t + 1) in contra.
      rewrite Nat_sub_add in contra.
      rewrite Nat.mul_sub_distr_l in contra.
      rewrite (Nat.mul_comm 2 ((6*k+4)/2)) in contra.
      rewrite Nat_mul_div in contra.
      lia.
      auto.
    }
    {
      destruct (j <=? (6 * k + 4) / 2) as []eqn:j_up.
      (* case 3 *)
      intro contra.
      apply f_equal with (f := fun t => t + 1) in contra.
      rewrite Nat_sub_add in contra.
      symmetry in contra.
      apply odd_even_lem in contra.
      assumption.
      (* case 4*)
      intro contra.
      apply f_equal with (f := fun t => t + 1) in contra.
      rewrite Nat_sub_add in contra.
      rewrite Nat.mul_comm in contra.
      symmetry in contra.
      rewrite Nat_sub_add in contra.
      rewrite Nat.mul_comm in contra.
      apply f_equal with (f := fun t => t / 2) in contra.
      rewrite Nat.div_mul in contra.
      symmetry in contra.
      rewrite Nat.div_mul in contra.
      apply f_equal with (f := fun t => t + (6 * k + 4) / 2) in contra.
      rewrite Nat_sub_add in contra.
      symmetry in contra.
      rewrite Nat_sub_add in contra.
      symmetry in contra.
      contradiction.
      auto.
      auto.
    }
  }
  {
    (*Dia should not attack*)
    unfold DiagonalCheck.
    unfold ChessMethod1.
    intros.
    destruct (i <=? (6 * k + 4) / 2) as []eqn:i_up.
    {
      destruct (j <=? (6 * k + 4) / 2) as []eqn:j_up.
      (* case D1 *)
      apply deMorgan2b.
      split.
      {
        rewrite double_to_plus.
        apply not_eq_sym.
        rewrite double_to_plus.
        rewrite Nat.add_assoc.
        intro contra.
        apply f_equal with (f := fun t => t - i) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_comm in contra.
        symmetry in contra.
        rewrite Nat.add_sub in contra.
        apply f_equal with (f := fun t => t - j) in contra.
        rewrite Nat.add_sub in contra.
        symmetry in contra.
        rewrite Nat.add_sub in contra.
        contradiction.
      }
      {
        rewrite <- (Nat.mul_1_l j) at 2.
        rewrite <- Nat.mul_add_distr_r.
        rewrite Nat.mul_comm.
        apply not_eq_sym.
        rewrite <- (Nat.mul_1_l i) at 1.
        rewrite Nat.add_comm.
        rewrite <- Nat.mul_add_distr_r.
        rewrite Nat.mul_comm.
        intros contra.
        apply f_equal with (f := fun t => t / (2 + 1)) in contra.
        rewrite Nat.div_mul in contra.
        symmetry in contra.
        rewrite Nat.div_mul in contra.
        symmetry in contra.
        contradiction.
        lia.
        lia.
      }
      (* case D2 *)
      apply deMorgan2b.
      split.
      {
        intro contra.
        rewrite (double_to_plus i) in contra.
        rewrite Nat.add_assoc in contra.
        apply f_equal with (f := fun t => t - i) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        apply f_equal with (f := fun t => t + (2*((6*k+4)/2))) in contra.
        rewrite Nat_sub_add in contra.
        rewrite (Nat.mul_comm 2 ((6*k+4)/2))in contra.
        rewrite Nat_mul_div in contra.
        lia.
        auto.
      }
      {
        intro contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite <- (Nat.mul_1_l j) in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        rewrite <- (Nat.mul_1_l i) in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        replace (1+2) with 3 in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.
        rewrite (Nat.mul_comm 2 ((6*k+4)/2))in contra.
        rewrite Nat_mul_div in contra.
        lia.
        auto.
        auto.
      }
    }
    {
      destruct (j <=? (6 * k + 4) / 2) as []eqn:j_up.
      (* case D3 *)
      apply deMorgan2b.
      split.
      {
        intro contra.
        rewrite (double_to_plus j) in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat.add_assoc in contra.
        rewrite (Nat.add_comm j (2 * (i - (6 * k + 4) / 2) - 1))in contra.
        apply f_equal with (f := fun t => t - j) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite (Nat.mul_comm 2 ((6*k+4)/2))in contra.
        rewrite Nat_mul_div in contra.
        lia.
        auto.
      }
      {
        intro contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite <- (Nat.mul_1_l j) in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        rewrite <- (Nat.mul_1_l i) in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        replace (1+2) with 3 in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.
        rewrite (Nat.mul_comm 2 ((6*k+4)/2))in contra.
        rewrite Nat_mul_div in contra.
        lia.
        auto.
        auto.
      }
      (* case D4 *)
      apply deMorgan2b.
      split.
      {
        intro contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite <- Nat.add_assoc in contra.
        rewrite (Nat.add_comm i 1) in contra.
        rewrite Nat.add_assoc in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_sub_add in contra.
        rewrite double_to_plus in contra.
        rewrite (double_to_plus i) in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + (2*((6*k+4)/2))) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat.add_assoc in contra.
        rewrite (Nat.add_comm j (i+i))in contra.
        apply f_equal with (f := fun t => t - j) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_comm in contra.
        apply f_equal with (f := fun t => t - i) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        symmetry in contra.
        contradiction.
      }
      {
        intro contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite <- Nat.add_assoc in contra.
        rewrite (Nat.add_comm j 1) in contra.
        rewrite Nat.add_assoc in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_add_sub_assoc in contra.
        rewrite Nat.add_comm in contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + (2*((6*k+4)/2))) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat_sub_add in contra.
        rewrite <- (Nat.mul_1_l j)in contra at 1.
        rewrite <- (Nat.mul_1_l i)in contra at 1.
        rewrite <- Nat.mul_add_distr_r in contra.
        rewrite <- Nat.mul_add_distr_r in contra.
        replace (1+2) with 3 in contra.
        rewrite Nat.mul_comm in contra.
        rewrite (Nat.mul_comm 3 i) in contra.
        apply f_equal with (f := fun t => t / 3) in contra.
        rewrite Nat.div_mul in contra.
        rewrite Nat.div_mul in contra.
        symmetry in contra.
        contradiction.
        auto.
        auto.
        auto.
      }
    }
  }
Qed.

Theorem QueensFinal_6k5:
  forall (k: nat), 
    (6*k+5)>3 ->
    (QueensSolution_expand (6*k+5) (6*k+4) (ChessMethod1 (6*k+4))).
Proof.
  unfold QueensSolution_expand.
  unfold ChessMethod1.
  intros.
  split.
  {
    (* Column should not attack *)
    destruct (i <=? (6 * k + 4) / 2) as []eqn:i_up.
    {
      (* case up *)
      lia.
    }
    {
      (* case down *)
      intro contra.
      apply leb_complete_conv in i_up.
      apply f_equal with (f := fun t => t + 1) in contra.
      rewrite Nat_sub_add in contra.
      rewrite <- Nat.add_assoc in contra.
      replace (1 + 1) with 2 in contra.
      rewrite Nat.mul_sub_distr_l in contra.
      apply f_equal with (f := fun t => t + (2*((6*k+4)/2))) in contra.
      rewrite Nat_sub_add in contra.
      rewrite (Nat.mul_comm 2 ((6*k+4)/2)) in contra.
      rewrite Nat_mul_div in contra.
      lia.
      auto.
      auto.
    }
  }
  {
    (* Dia should not attack *)
    unfold DiagonalCheck.
    apply deMorgan2b.
    destruct (i <=? (6 * k + 4) / 2) as []eqn:i_up.
    {
      (* case up *)
      split.
      {
        lia.
      }
      {
        lia.
      }
    }
    {
      (* case down *)
      apply leb_complete_conv in i_up.
      split.
      {
        intros contra.
        rewrite (Nat.add_comm (6*k+5) i) in contra.
        rewrite (Nat.add_comm (6*k+5) (2*(i-(6*k+4)/2)-1)) in contra.
        apply f_equal with (f := fun t => t - (6 * k + 5)) in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.add_sub in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite (Nat.mul_comm 2 ((6*k+4)/2)) in contra.
        rewrite Nat_mul_div in contra.
        lia.
        auto.
      }
      {
        intro contra.
        rewrite Nat_add_sub_assoc in contra.
        apply f_equal with (f := fun t => t + 1) in contra.
        rewrite Nat_sub_add in contra.
        rewrite Nat.mul_sub_distr_l in contra.
        rewrite (Nat.mul_comm 2 ((6*k+4)/2)) in contra.
        rewrite Nat_mul_div in contra.
        lia.
        auto.
      }
    }
  }
Qed.     
