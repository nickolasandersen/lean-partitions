import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal

import Mathlib.NumberTheory.LSeries.Dirichlet

open Nat BigOperators Finset Finset.Nat

def Bernoulli : ℕ → ℚ
  | 0 => 1
  | m + 1 =>
    (- ∑ k : Fin (m+1), (m+2).choose k * Bernoulli k) / (m+2)

#eval Bernoulli 0 -- 1
#eval Bernoulli 1 -- -1/2
#eval Bernoulli 2 -- 1/6
#eval Bernoulli 3 -- 0
#eval Bernoulli 4 -- -1/30
#eval Bernoulli 5 -- 0

theorem bernoulli_def (m : ℕ) : (- ∑ k : Fin (m+1), (m+2).choose k * Bernoulli k) / (m+2) = Bernoulli (m+1) := rfl

theorem bernoulli_def_range (m : ℕ) : (- ∑ k in range (m+1), (m+2).choose k * Bernoulli k) / (m+2) = Bernoulli (m+1) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply bernoulli_def

theorem bernoulli_def' (m : ℕ) : ∑ k ∈ range (m + 1), (m+2).choose k * Bernoulli k = - (m+2) * Bernoulli (m+1) := by
  calc ∑ k ∈ range (m + 1), ↑((m + 2).choose ↑k) * Bernoulli ↑k
      = - (m+2) * ((-∑ k ∈ range (m + 1), ↑((m + 2).choose ↑k) * Bernoulli ↑k) / (m+2)) := by
        field_simp; ring
    _ = - (m+2) * Bernoulli (m+1) := by rw [bernoulli_def_range]


theorem binom_bernoulli_sum_eq_zero : ∑ k ∈ range (m + 1), ↑((m + 1).choose k) * Bernoulli k = if (m=0) then 1 else 0 := by
  match m with
  | 0 => simp; rfl
  | m+1 =>
    rw [Finset.sum_range_succ, bernoulli_def']
    simp; ring

theorem binom_bernoulli_sum_eq_zero'' : ∑ k ∈ range m, ↑(m.choose k) * Bernoulli k = if (m=1) then 1 else 0 := by
  match m with
  | 0 => rfl
  | m+1 => rw [binom_bernoulli_sum_eq_zero]; simp

theorem binom_bernoulli_sum_eq_zero' : ∑ k ∈ range (m + 2), ↑((m + 2).choose k) * Bernoulli k = 0 := by
  rw [binom_bernoulli_sum_eq_zero]; simp

lemma triangle_range (m : ℕ) : ∀ x y : ℕ, x ∈ range m ∧ y ∈ range (m - x) ↔ x ∈ range (m - y) ∧ y ∈ range m := by
  simp
  have H : forall x y : ℕ, x < m ∧ y < m - x → x < m - y ∧ y < m := by
    intro x y ⟨_, ylt⟩
    constructor
    . exact Nat.lt_sub_of_add_lt (Nat.add_lt_of_lt_sub' ylt)
    calc y < m - x := ylt
      _ ≤ m := by apply Nat.sub_le
  intro x y
  constructor
  . apply H
  nth_rewrite 1 [and_comm]; nth_rewrite 2 [and_comm]
  apply H

lemma sum_convolution (m : ℕ) (f : ℕ → ℕ → ℚ) :
  ∑ i in range m, ∑ j in range (m-i), f i j = ∑ j in range m, ∑ i in range (m-j), f i j := by
  rw [Finset.sum_comm']
  apply triangle_range

lemma range_reverse (m : ℕ) : ∀ a ∈ range (m+1), m-a ∈ range (m+1) := by
  simp; intro a ain
  rw [Nat.sub_lt_iff_lt_add]
  linarith
  exact le_of_lt_succ ain

lemma range_reverse_sub (m : ℕ) : ∀ a ∈ range (m+1), m - (m-a) = a := by
  simp; intro a ain
  rw [Nat.sub_sub_eq_min, Nat.min_eq_right]
  exact le_of_lt_succ ain

lemma sum_reverse (m : ℕ) (f : ℕ → ℚ):
  ∑ i in range (m+1), f i = ∑ i in range (m+1), f (m-i) := by
  apply Finset.sum_nbij' (fun k => m-k) (fun k => m-k)
  . apply range_reverse
  . apply range_reverse
  . apply range_reverse_sub
  . apply range_reverse_sub
  intro k kin
  congr; symm
  apply range_reverse_sub
  exact kin

lemma range_succ {m : ℕ} (h : k ∈ range (m+1)) : m - k + 1 = m + 1 - k := by
  rw [← Nat.sub_add_comm]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp h)

lemma range_succ' {m : ℕ} (h : k ∈ range m) : m - k + 1 = m + 1 - k := by
  rw [← Nat.sub_add_comm]
  exact Finset.mem_range_le h

lemma choose_mul_swap {a b c : ℕ} (h1 : b ≤ a) (h2 : c ≤ a - b) : a.choose b * (a-b).choose c = a.choose c * (a-c).choose b := by
  have c_le_a : c ≤ a := by
    calc c ≤ a - b := h2
      _ ≤ a := by apply Nat.sub_le
  rw [← choose_symm h1, choose_mul (Nat.sub_le a b) h2, Nat.sub_sub, add_comm, ← Nat.sub_sub, choose_symm]
  rw [Nat.le_sub_iff_add_le' h1] at h2
  . rw [Nat.le_sub_iff_add_le c_le_a]; assumption

lemma choose_mul_swap_rat {a b c : ℕ} (h1 : b ≤ a) (h2 : c ≤ a - b) : (a.choose b : ℚ) * (a-b).choose c = a.choose c * (a-c).choose b := by
  rw [← cast_mul, choose_mul_swap h1 h2, cast_mul]

lemma L {m x : ℕ} (h : x ∈ range (m+2)) :
  ∑ k ∈ range (m + 2 - x), Bernoulli k * ((m + 2).choose k) * ((m + 2 - k).choose (x + 1))
    = Bernoulli (m+1-x) * ((m + 2).choose (m+1-x)) + ↑(if x = m then m + 2 else 0) := by
  have : m + 1 - x + 1 = m + 2 - x := range_succ h
  rw [← this, Finset.sum_range_succ (fun k => Bernoulli k * ((m + 2).choose k) * ((m + 2 - k).choose (x + 1))) (m+1-x), add_comm]
  congr 1
  . have : m + 2 - (m + 1 - x) = x + 1 := by
      calc m + 2 - (m + 1 - x) = (m + 1 - (m + 1 - x)) + 1 := by
            rw [add_comm (m+1 - _) 1, ← Nat.add_sub_assoc, add_comm 1 _]
            apply sub_le
        _ = x + 1 := by rw [range_reverse_sub _ _ h]
    rw [this]; simp
  calc ∑ k ∈ range (m + 1 - x), Bernoulli k * ↑((m + 2).choose k) * ↑((m + 2 - k).choose (x + 1))
      =  ((m+2).choose (x+1)) * ∑ k ∈ range (m + 1 - x), ((m+1-x).choose k) * Bernoulli k := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k kin
        have k_le_m : k ≤ m + 2 := by
          calc k ≤ m+1-x := mem_range_le kin
            _ ≤ m+1 := sub_le (m + 1) x
            _ ≤ m+2 := by simp only [add_le_add_iff_left, one_le_ofNat]
        have x_le_mk : x+1 ≤ m + 2 - k := by
          apply mem_range_le at kin
          rw [Nat.le_sub_iff_add_le] at *
          rw [add_comm, ← add_assoc]
          simp only [add_le_add_iff_right]; exact kin
          exact Finset.mem_range_succ_iff.mp h
          exact k_le_m
        rw [mul_assoc, choose_mul_swap_rat k_le_m x_le_mk, mul_comm, ← mul_assoc]
        congr 4
        simp_all only [mem_range, reduceSubDiff]
    _ = ↑(if x = m then m + 2 else 0) := by
      rw [binom_bernoulli_sum_eq_zero'']
      simp only [cast_ite, cast_add, cast_ofNat]
      rw [mul_ite]
      apply ite_congr
      . rw [eq_iff_iff]
        constructor <;> intro H
        . rw [Nat.sub_eq_iff_eq_add, add_comm] at H
          linarith
          exact Nat.le_of_lt_succ (mem_range.mp h)
        rw [H]; simp only [add_tsub_cancel_left]
      . intro x_eq_m
        rw [x_eq_m]
        simp only [choose_succ_self_right, cast_add, cast_one, mul_one]; ring
      . simp only [mul_zero, CharP.cast_eq_zero, implies_true]

theorem Sum_range_pow (n m : ℕ) :
  (m + 1) * (∑ l in range n, (l : ℚ) ^ m) =
      ∑ k in range (m + 1), Bernoulli k * ((m + 1).choose k) * (n : ℚ) ^ (m + 1 - k) := by
  match n with
  | 0 =>
    simp only [range_zero, sum_empty, mul_zero]; symm
    apply Finset.sum_eq_zero
    intro x xin
    simp only [_root_.mul_eq_zero, cast_eq_zero, pow_eq_zero_iff', ne_eq, true_and]; right
    apply mem_range_sub_ne_zero xin
  | n+1 =>
    cases' m with m
    . simp; rw [Bernoulli]; ring
    rw [sum_range_succ, mul_add, Sum_range_pow]
    symm
    let a : ℕ → ℚ := fun k => Bernoulli k * ((m + 2).choose k)
    calc
      ∑ k ∈ range (m + 2), Bernoulli k * ((m + 1 + 1).choose k) * ↑(n + 1) ^ (m + 2 - k)
        = ∑ k in range (m + 2), a k * ↑(n + 1) ^ (m + 2 - k) := by simp
      _ = ∑ k in range (m + 2), (∑ l in range (m+2-k), a k * ((m+2-k).choose (l+1) * n^(l+1)) + a k) := by
        apply Finset.sum_congr rfl
        intro k kin;
        calc a k * ↑(n + 1) ^ (m + 2 - k)
            = ∑ l in range (m+3-k), a k * ((m+2-k).choose l * n^l) := by
              rw [← Finset.mul_sum _ _ (a k)]
              congr 1
              simp only [cast_add, cast_one]
              rw [add_pow (n:ℚ) 1 (m+2-k)]
              apply Finset.sum_congr
              . congr
                apply range_succ' kin
              intro x _
              rw [mul_comm, one_pow, mul_one]
          _ = ∑ l ∈ range (m + 2 - k), a k * ((m + 2 - k).choose (l + 1) * ↑n ^ (l + 1)) + a k := by
            repeat rw [← mul_sum _ _ (a k)]
            nth_rewrite 3 [← mul_one (a k)]
            rw [← mul_add]
            congr 1
            have : m + 2 - k + 1 = m + 3 - k := range_succ' kin
            rw [← this, Finset.sum_range_succ' (fun i => ((m + 2 - k).choose i:ℚ) * n ^ i) (m+2-k)]
            simp only [choose_zero_right, cast_one, pow_zero, mul_one]
      _ = ∑ k in range (m + 2), ∑ l in range (m+2-k), a k * ((m+2-k).choose (l+1) * n^(l+1)) + ∑ k in range (m + 2), a k:= Finset.sum_add_distrib
      _ = ∑ k in range (m + 2), ∑ l in range (m+2-k), a k * ((m+2-k).choose (l+1) * n^(l+1)):= by
        rw [add_right_eq_self]
        dsimp [a]
        rw [← binom_bernoulli_sum_eq_zero']
        apply sum_congr rfl
        intro _ _; ring
      _ = ∑ l in range (m + 2), ∑ k in range (m+2-l), a k * ((m+2-k).choose (l+1) * n^(l+1)):= by rw [sum_convolution]
      _ = ∑ l in range (m + 2), ∑ k in range (m+2-l), a k * (m+2-k).choose (l+1) * n^(l+1):= by simp_rw [mul_assoc]
      _ = ∑ k in range (m + 2), a k * ↑n ^ (m + 2 - k) + (↑m + 2) * ↑n ^ (m+1) := by
        -- REWORK THIS
        have H1 : ∑ k in range (m + 2), a k * ↑n ^ (m + 2 - k) = ∑ k in range (m + 2), a (m+1-k) * ↑n ^ (k+1) := by
          have := sum_reverse (m+1) (fun k => a k * ↑n^(m+2-k))
          rw [this]
          apply sum_congr rfl
          intro k kin; congr;
          nth_rewrite 2 [← range_reverse_sub (m+1) k]
          rw [← Nat.sub_add_comm]
          apply Nat.sub_le
          exact kin
        have H2 : ∑ k ∈ range (m + 2), a (m + 1 - k) * ↑n ^ (k + 1) + (↑m + 2) * ↑n ^ (m+1) = ∑ k ∈ range (m + 2), (a (m + 1 - k) + (if (k=m) then (m+2) else 0)) * ↑n ^ (k + 1) := by
          symm
          calc ∑ k ∈ range (m + 2), (a (m + 1 - k) + ↑(if k = m then m + 2 else 0)) * ↑n ^ (k + 1)
              = ∑ k ∈ range (m + 2), (a (m + 1 - k)*↑n ^ (k + 1) + ↑(if k = m then m + 2 else 0)*↑n ^ (k + 1))  := by
                apply Finset.sum_congr rfl
                intro x _
                rw [add_mul]
            _ = _ := by
              rw [Finset.sum_add_distrib]
              congr 1
              simp only [cast_ite, cast_add, cast_ofNat, CharP.cast_eq_zero, ite_mul, zero_mul, sum_ite_eq', mem_range, lt_add_iff_pos_right, ofNat_pos, ↓reduceIte]
        rw [H1, H2]
        --
        apply sum_congr rfl
        intro x xin
        rw [← Finset.sum_mul]
        congr
        exact L xin
      _ = ∑ k ∈ range (m + 2), Bernoulli k * ((m + 2).choose k) * ↑n ^ (m + 2 - k) + (↑(m + 1) + 1) * ↑n ^ (m + 1) := by
        simp; left; ring








example {a b : ℕ → ℚ} : ∑ k ∈ range m, a k * b k  = ∑ k ∈ range m, b k * a k := by
  simp_rw [mul_comm]
  -- apply Finset.sum_congr rfl; intro _ _
  -- rw [mul_comm]

example {a b : ℕ → ℚ} : ∑ k ∈ range m, a k * b k  = ∑ k ∈ range m, b k * a k := by
  conv_lhs =>
    enter [2, x]
    rw [mul_comm]


#eval (∑ l in range 4, (l : ℚ) ^ 2) -- 14
#eval ∑ k in range (2 + 1), Bernoulli k * ((2 + 1).choose k) * (4 : ℚ) ^ (2 + 1 - k) / (2 + 1) -- 14

def B : ℕ → ℚ := fun n => ∑ k ∈ divisors (2*n), if (Nat.Prime (k+1)) then 1/(k+1) else 0

lemma lt_prime_power {p k : ℕ} (pp : Nat.Prime p) (h : k ≥ 2) : k + 1 < p^k := by
  match k with
  | 0 => linarith
  | 1 => linarith
  | 2 =>
    calc 3 < 2^2 := by norm_num
      _ ≤ p^2 := by
        rw [pow_le_pow_iff_left (by norm_num) (by norm_num) (by norm_num)]
        exact (Prime.two_le pp)
  | k+3 =>
    calc k + 3 + 1 = ((k+2) + 1) + 1 := by ring
      _ < p^(k+2) + 1 := by apply add_lt_add_right (lt_prime_power pp (by linarith))
      _ ≤ p^(k+2) + p^(k+2) := add_le_add_left (one_le_pow (k+2) p (Prime.pos pp)) (p^(k+2))
      _ = 2*p^(k+2) := by ring
      _ ≤ p*p^(k+2) := Nat.mul_le_mul_right _ (Prime.two_le pp)
      _ = p^(k+3) := by ring

lemma le_prime_power {p k : ℕ} (pp : Nat.Prime p) : k + 1 ≤ p^k := by
  match k with
  | 0 => simp only [zero_add, pow_zero, le_refl]
  | 1 => simp; exact (Prime.two_le pp)
  | k+2 => apply le_of_lt (lt_prime_power pp (by linarith))

lemma le_prime_power' {p k : ℕ} (pp : Nat.Prime p) (h : k ≥ 3) : k + 1 ≤ p^(k-1) := by
  sorry

lemma padic_val_lemma_a {p k : ℕ} [pp : Fact p.Prime] : 0 ≤ padicValRat p (p^k / (k+1)) := by
  rw [padicValRat.div, padicValRat.pow, padicValRat.self, mul_one]
  . rw [le_sub_iff_add_le, zero_add]
    norm_cast
    calc padicValNat p (k+1) ≤ Nat.log p (k+1) := padicValNat_le_nat_log _
      _ ≤ Nat.log p (p^k) := log_mono_right (le_prime_power (Fact.elim pp))
      _ = k := by rw [log_pow (Prime.one_lt (Fact.elim pp))]
  . apply Prime.one_lt (Fact.elim pp)
  . exact Ne.symm (NeZero.ne' (p:ℚ))
  . apply pow_ne_zero k (NeZero.ne' (p:ℚ)).symm
  linarith

lemma padic_val_lemma_b {p k : ℕ} [pp : Fact p.Prime] (h : k ≥ 2) : 1 ≤ padicValRat p (p^k / (k+1)) := by
  rw [padicValRat.div, padicValRat.pow, padicValRat.self, mul_one]
  by_cases H : k ≤ 2
  . have keq : k = 2 := by linarith
    rw [keq]; simp; norm_num
    rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
    simp only [Int.reduceSub]
    by_cases H' : p = 3
    . rw [H']; norm_cast; norm_num;
    norm_cast
    rw [@padicValNat_primes p 3 _ _]
    simp;
    exact H'
  . rw [le_sub_iff_add_le]
    norm_cast
    calc 1 + padicValNat p (k+1) ≤ 1 + Nat.log p (k+1) := by simp; apply padicValNat_le_nat_log
      _ ≤  1 + Nat.log p (p^(k-1)) := by
        simp only [add_le_add_iff_left]
        apply log_mono_right (le_prime_power' (Fact.elim pp) _)
        linarith
      _ = k := by rw [log_pow (Prime.one_lt (Fact.elim pp)), ← Nat.add_sub_assoc, add_comm, add_tsub_cancel_right]; linarith
  . apply Prime.one_lt (Fact.elim pp)
  . exact Ne.symm (NeZero.ne' (p:ℚ))
  . apply pow_ne_zero k (NeZero.ne' (p:ℚ)).symm
  linarith

theorem prime_mul_bernoulli (p m : ℕ) [pp : Fact p.Prime] : padicValRat p (p * Bernoulli m) ≥ 0 := by
  match m with
  | 0 =>
    simp_rw [Bernoulli]
    simp
  | m+1 =>
    have lem10 := Sum_range_pow p (m+1)
    rw [Finset.sum_range_succ _ (m+1)] at lem10
    -- rw [choose_succ_self_right] at lem10
    -- rw [Nat.add_sub_assoc, Nat.add_sub_cancel'] at lem10
    simp at lem10
    nth_rewrite 4 [add_comm] at lem10
    rw [← sub_eq_iff_eq_add, mul_assoc] at lem10
    nth_rewrite 2 [mul_comm] at lem10
    rw [mul_assoc] at lem10
    symm at lem10
    conv_lhs at lem10 =>
      enter [1]
      ring; rw [add_comm]
    have : p * Bernoulli (m+1) = ∑ l ∈ range p, l ^ (m + 1) - (∑ x ∈ range (m + 1), Bernoulli x * ↑((m + 2).choose x) * ↑p ^ (m + 2 - x))/(m+2) := by
      calc
        p * Bernoulli (m+1) = ((↑m + 2) * ∑ l ∈ range p, ↑l ^ (m + 1) - ∑ x ∈ range (m + 1), Bernoulli x * ↑((m + 1 + 1).choose x) * ↑p ^ (m + 1 + 1 - x))/(m+2) := by
          sorry
          -- field_simp
          -- rw [mul_comm, lem10]
        _ = _ := by
          field_simp
          rw [mul_comm]
    rw [this]
    sorry



theorem prime_mul_even_bernoulli_sum_pow (p m : ℕ) [pp : Fact p.Prime] :
  p * Bernoulli (2*m) % p = (∑ k ∈ range (2*m), k^p) % p := by
  match m with
  | 0 => simp
  | m+1 =>
    sorry

theorem bernoulli_add_prime_sum (m : ℕ) : (Bernoulli (2*m) + B (2*m)).den = 1 := by
  sorry

theorem exists_primitive_root_mod_p {p : ℕ} [pp : Fact p.Prime] : ∃ g : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := by
  have dom : IsDomain (ZMod p) := ZMod.instIsDomain p
  have cyc : IsCyclic (ZMod p)ˣ := instIsCyclicUnitsOfFinite
  obtain ⟨g, hg⟩ := cyc
  exact ⟨g, hg⟩

theorem primitive_root_generates {p : ℕ} [pp : Fact p.Prime] {g : (ZMod p)ˣ} (h : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
  Subgroup.zpowers g = ⊤ := by
  apply Subgroup.ext
  intro x
  constructor
  . intro _
    apply Subgroup.mem_top
  . intro _
    apply h

def S : ℕ → ℕ → ℕ := fun m p => ∑ k ∈ range p, k^m


example {A B : ℝ} (h1 : A ≥ 0) (h2 : B ≥ 0)
  (h3 : 52416000+195660*A-48*B ≥ 0)
  (h4 : 6609020221440+44656110*A-15040*B ≥ 0)
  (h5 : 143820*B+437824977408000-982499328*A ≥ 0) :
  -23571622401187840*A+1067719461857731896421100256000-13217772238272*B ≥ 0 := by
  linarith only [h3, h5]


-- #eval Bernoulli (2*5) + B 5
-- #eval Bernoulli (2*6) + B 6
-- #eval Bernoulli (2*7) + B 7





-- OLD VERSION
--

-- lemma lt_of_range_diff (m : ℕ) : y ∈ range m \ range (m-x) → x+y ≥ m := by
--   rw [Finset.mem_sdiff, mem_range, mem_range]
--   push_neg
--   rw [Nat.sub_le_iff_le_add, add_comm]
--   simp

-- lemma sum_sum_expand (m : ℕ) (f h : ℕ → ℕ → ℚ) (heq: h = fun i => (fun j => ite (i+j < m) (f i j) 0)) :
--   ∑ i in range m, ∑ j in range (m-i), f i j
--       = ∑ i in range m, ∑ j in range m, h i j := by
--   apply sum_congr rfl
--   intro i _
--   apply Finset.sum_subset_zero_on_sdiff (by simp)
--   . intro x xin
--     have H := lt_of_range_diff m xin
--     rw [heq]; simp
--     intro lt
--     exfalso; linarith
--   intro x xin
--   symm
--   rw [heq]
--   apply ite_cond_eq_true
--   rw [mem_range] at xin
--   refine eq_true ?hfg.h.h
--   rw [Nat.lt_sub_iff_add_lt, add_comm] at xin
--   assumption

-- lemma sum_sum_expand' (m : ℕ) (f h : ℕ → ℕ → ℚ) (heq: h = fun j => (fun i => ite (j+i < m) (f j i) 0)) :
--   ∑ i in range m, ∑ j in range (m-i), f j i
--       = ∑ i in range m, ∑ j in range m, h j i := by
--   apply sum_congr rfl
--   intro i _
--   apply Finset.sum_subset_zero_on_sdiff (by simp)
--   . intro x xin
--     have H := lt_of_range_diff m xin
--     rw [heq]; simp
--     intro lt
--     exfalso; linarith
--   intro x xin
--   symm
--   rw [heq]
--   apply ite_cond_eq_true
--   rw [mem_range] at xin
--   refine eq_true ?hfg.h.h
--   rw [Nat.lt_sub_iff_add_lt] at xin
--   assumption

-- lemma sum_convolution' (m : ℕ) (f : ℕ → ℕ → ℚ) :
--   ∑ i in range m, ∑ j in range (m-i), f i j = ∑ j in range m, ∑ i in range (m-j), f i j := by
--   let h : ℕ → ℕ → ℚ := fun i => (fun j => ite (i+j < m) (f i j) 0)
--   calc
--     ∑ i in range m, ∑ j in range (m-i), f i j
--       = ∑ i in range m, ∑ j in range m, h i j := by rw [sum_sum_expand]; simp
--     _ = ∑ j in range m, ∑ i in range m, h i j := by rw [Finset.sum_comm]
--     _ = ∑ j in range m, ∑ i in range (m-j), f i j := by rw [← sum_sum_expand']; simp
