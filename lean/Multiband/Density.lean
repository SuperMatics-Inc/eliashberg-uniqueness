import KayThermo.Convex

noncomputable section
open scoped BigOperators

namespace Multiband
open KayThermo

/-- A real vector indexed by the positive-frequency band vertices. -/
abbrev Density (N : ℕ) := Fin N → ℝ

def rowHalf {N : ℕ} (D : Fin N → Fin N → ℝ) (n : Fin N) : ℝ :=
  (1 / 2 : ℝ) * ∑ m, if n ≠ m then D n m else 0

def qForm {N : ℕ} (w L : Density N) (W : Fin N → Fin N → ℝ)
    (y : Density N) : ℝ :=
  (∑ n, (w n + 2 * L n) * y n ^ 2) - ∑ n, ∑ m, W n m * y n * y m

/-- The even planar energy, with D and W already assembled from A and B. -/
def planar {N : ℕ} (w : Density N) (D W : Fin N → Fin N → ℝ)
    (s c : Density N) : ℝ :=
  (∑ n, w n * (1 - c n)) +
    (1 / 2 : ℝ) * (∑ n, ∑ m, if n ≠ m then D n m * (1 - c n * c m) else 0) -
    (1 / 2 : ℝ) * ∑ n, ∑ m, W n m * s n * s m

/-- Symmetry of D supplies the two equal halves in the row-sum identity. -/
theorem rowHalf_identity {N : ℕ} (D : Fin N → Fin N → ℝ)
    (hD : ∀ n m, D n m = D m n) (ρ : Density N) :
    (∑ n, rowHalf D n * ρ n) =
      (1 / 4 : ℝ) * ∑ n, ∑ m, if n ≠ m then D n m * (ρ n + ρ m) else 0 := by
  classical
  have hswap : (∑ n, ∑ m, if n ≠ m then D n m * ρ m else 0) =
      ∑ n, ∑ m, if n ≠ m then D n m * ρ n else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    simp only [hD m n, ne_comm]
  have hrow : (∑ n, rowHalf D n * ρ n) =
      (1 / 2 : ℝ) * ∑ n, ∑ m, if n ≠ m then D n m * ρ n else 0 := by
    simp only [rowHalf, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> ring
  have hsplit : (∑ n, ∑ m, if n ≠ m then D n m * (ρ n + ρ m) else 0) =
      (∑ n, ∑ m, if n ≠ m then D n m * ρ n else 0) +
      (∑ n, ∑ m, if n ≠ m then D n m * ρ m else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> ring
  rw [hrow, hsplit, hswap]
  ring

/-- Hidden-convexity substitution in algebraic spin coordinates s >= 0, c >= 0. -/
theorem hidden_substitution {N : ℕ} (w : Density N) (D W : Fin N → Fin N → ℝ)
    (hD : ∀ n m, D n m = D m n) (s c : Density N)
    (hs : ∀ n, 0 ≤ s n) (hc : ∀ n, 0 ≤ c n)
    (hunit : ∀ n, s n ^ 2 + c n ^ 2 = 1) :
    planar w D W s c = Gen w (rowHalf D) D W (fun n => s n ^ 2) := by
  classical
  have hsqrt (n : Fin N) : Real.sqrt (1 - s n ^ 2) = c n := by
    have he : 1 - s n ^ 2 = c n ^ 2 := by linarith [hunit n]
    rw [he, Real.sqrt_sq (hc n)]
  have hprod (n m : Fin N) : Real.sqrt (s n ^ 2 * s m ^ 2) = s n * s m := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hs n), Real.sqrt_sq (hs m)]
  have hpair : (1 / 2 : ℝ) * (∑ n, ∑ m,
      if n ≠ m then D n m * (1 - c n * c m) else 0) =
      (∑ n, rowHalf D n * s n ^ 2) + (1 / 4 : ℝ) *
        (∑ n, ∑ m, if n ≠ m then D n m * (c n - c m) ^ 2 else 0) := by
    rw [rowHalf_identity D hD]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs
    · linear_combination -(D n m / 4) * (hunit n) - (D n m / 4) * (hunit m)
    · ring
  simp only [planar, Gen, hsqrt, hprod]
  rw [hpair]
  simp only [mul_assoc]
  ring

/-- Under the stated signs, the density functional has a unique minimum on the closed cube. -/
theorem density_unique_minimum {N : ℕ} (w L : Density N)
    (D W : Fin N → Fin N → ℝ) (hw : ∀ n, 0 < w n)
    (hD : ∀ n m, n ≠ m → 0 ≤ D n m) (hW : ∀ n m, 0 ≤ W n m) :
    ∃! ρ : Density N, ρ ∈ cube N ∧ ∀ σ ∈ cube N, Gen w L D W ρ ≤ Gen w L D W σ := by
  obtain ⟨ρ, hρ, hmin⟩ := Gen_exists_min w L D W
  refine ⟨ρ, ⟨hρ, hmin⟩, ?_⟩
  intro σ hσ
  exact Gen_min_unique w L D W hw hD hW hσ.1 hρ hσ.2 hmin

/-- Decompose the density energy into its quadratic part and weighted squares. -/
theorem density_decomposition {N : ℕ} (w L : Density N)
    (D W : Fin N → Fin N → ℝ) (ρ : Density N) (hρ : ρ ∈ cube N) :
    Gen w L D W ρ = (1 / 2 : ℝ) * qForm w L W (fun n => Real.sqrt (ρ n)) +
      (1 / 2 : ℝ) * (∑ n, w n * (1 - Real.sqrt (1 - ρ n)) ^ 2) +
      (1 / 4 : ℝ) * (∑ n, ∑ m, if n ≠ m then D n m *
        (Real.sqrt (1 - ρ n) - Real.sqrt (1 - ρ m)) ^ 2 else 0) := by
  classical
  have hsingle (n : Fin N) : w n * (1 - Real.sqrt (1 - ρ n)) + L n * ρ n =
      (1 / 2 : ℝ) * ((w n + 2 * L n) * ρ n) +
        (1 / 2 : ℝ) * (w n * (1 - Real.sqrt (1 - ρ n)) ^ 2) := by
    have hsq := Real.sq_sqrt (sub_nonneg.mpr (hρ n).2)
    linear_combination -(w n / 2) * hsq
  have hsum := congrArg (fun f : Fin N → ℝ => ∑ n, f n) (funext hsingle)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hprod (n m : Fin N) : Real.sqrt (ρ n * ρ m) = Real.sqrt (ρ n) * Real.sqrt (ρ m) :=
    Real.sqrt_mul (hρ n).1 _
  simp only [Gen, qForm, Real.sq_sqrt (hρ _).1, hprod]
  simp_rw [mul_assoc]
  linarith [hsum]

/-- At linear stability the normal density is strictly preferred, including threshold. -/
theorem normal_strict_minimum {N : ℕ} (w L : Density N)
    (D W : Fin N → Fin N → ℝ) (hw : ∀ n, 0 < w n)
    (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    (hQ : ∀ y : Density N, 0 ≤ qForm w L W y)
    {ρ : Density N} (hρ : ρ ∈ cube N) (hne : ρ ≠ 0) : 0 < Gen w L D W ρ := by
  classical
  rw [density_decomposition w L D W ρ hρ]
  have hpair : 0 ≤ ∑ n, ∑ m, if n ≠ m then D n m *
      (Real.sqrt (1 - ρ n) - Real.sqrt (1 - ρ m)) ^ 2 else 0 := by
    apply Finset.sum_nonneg
    intro n _
    apply Finset.sum_nonneg
    intro m _
    split_ifs with hnm
    · exact mul_nonneg (hD n m hnm) (sq_nonneg _)
    · exact le_refl 0
  have hsq : 0 < ∑ n, w n * (1 - Real.sqrt (1 - ρ n)) ^ 2 := by
    have hex : ∃ n, ρ n ≠ 0 := by
      by_contra! hn
      exact hne (funext hn)
    obtain ⟨n, hn⟩ := hex
    apply Finset.sum_pos' (fun m _ => mul_nonneg (hw m).le (sq_nonneg _))
    refine ⟨n, Finset.mem_univ n, mul_pos (hw n) (sq_pos_of_ne_zero ?_)⟩
    intro he
    have hc := Real.sq_sqrt (sub_nonneg.mpr (hρ n).2)
    apply hn
    nlinarith
  have hq := hQ (fun n => Real.sqrt (ρ n))
  linarith

/-- A nonlinear negative-energy witness necessarily gives a negative quadratic direction. -/
theorem negative_density_implies_negative_quadratic {N : ℕ} (w L : Density N)
    (D W : Fin N → Fin N → ℝ) (hw : ∀ n, 0 < w n)
    (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    {ρ : Density N} (hρ : ρ ∈ cube N) (hneg : Gen w L D W ρ < 0) :
    ∃ y : Density N, qForm w L W y < 0 := by
  by_contra! hQ
  by_cases hz : ρ = 0
  · subst ρ
    simp [Gen] at hneg
  · have := normal_strict_minimum w L D W hw hD hQ hρ hz
    linarith

end Multiband
