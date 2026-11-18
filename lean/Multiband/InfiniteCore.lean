import Multiband.Phase

noncomputable section
open scoped BigOperators

namespace Multiband.InfiniteCore

/-- A finite-band finite-window Schur quadratic estimate. No scalar-band
specialization: the index type can be `Fin p × Fin k`. -/
theorem finite_schur {ι : Type*} [Fintype ι]
    (W : ι → ι → ℝ) (z : ι → ℝ) (C : ℝ)
    (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j ≤ C)
    (hcol : ∀ j, ∑ i, W i j ≤ C) :
    (∑ i, ∑ j, W i j * z i * z j) ≤ C * ∑ i, z i ^ 2 := by
  classical
  have hp : 2 * (∑ i, ∑ j, W i j * z i * z j) ≤
      ∑ i, ∑ j, (W i j * z i ^ 2 + W i j * z j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [mul_nonneg (hW i j) (sq_nonneg (z i - z j))]
  have hr : (∑ i, ∑ j, W i j * z i ^ 2) ≤ C * ∑ i, z i ^ 2 := by
    simp_rw [← Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  have hc : (∑ i, ∑ j, W i j * z j ^ 2) ≤ C * ∑ i, z i ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
  simp only [Finset.sum_add_distrib] at hp
  linarith

/-- The same estimate for the absolute value, valid for signed real vectors. -/
theorem finite_schur_abs {ι : Type*} [Fintype ι]
    (W : ι → ι → ℝ) (z : ι → ℝ) (C : ℝ)
    (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j ≤ C)
    (hcol : ∀ j, ∑ i, W i j ≤ C) :
    |∑ i, ∑ j, W i j * z i * z j| ≤ C * ∑ i, z i ^ 2 := by
  classical
  calc
    _ ≤ ∑ i, |∑ j, W i j * z i * z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |W i j * z i * z j| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, W i j * |z i| * |z j| := by
      simp only [abs_mul, abs_of_nonneg (hW _ _)]
    _ ≤ C * ∑ i, |z i| ^ 2 := finite_schur W (fun i => |z i|) C hW hrow hcol
    _ = C * ∑ i, z i ^ 2 := by simp only [sq_abs]

/-- The weighted coordinate change in the infinite proof, on any finite set. -/
theorem weighted_sqrt_mass {ι : Type*} [Fintype ι]
    (w ρ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hρ : ∀ i, 0 ≤ ρ i) :
    (∑ i, (Real.sqrt (w i * ρ i)) ^ 2) = ∑ i, w i * ρ i := by
  apply Finset.sum_congr rfl
  intro i _
  exact Real.sq_sqrt (mul_nonneg (hw i) (hρ i))

/-- Uniform lower weights turn weighted density mass into unweighted mass. -/
theorem weighted_mass_dominates {ι : Type*} [Fintype ι]
    (w ρ : ι → ℝ) (ν : ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hw : ∀ i, ν ≤ w i) :
    ν * (∑ i, ρ i) ≤ ∑ i, w i * ρ i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i) (hρ i)

/-- Finite-head mass is bounded independently of the density in the cube. -/
theorem head_mass_bound {ι : Type*} [Fintype ι]
    (w ρ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hρ : ∀ i, ρ i ≤ 1) :
    (∑ i, w i * ρ i) ≤ ∑ i, w i := by
  apply Finset.sum_le_sum
  intro i _
  simpa using mul_le_mul_of_nonneg_left (hρ i) (hw i)

/-- The coercive bound combines the tail estimate from compactness with the
finite head bound from the density cube. Both bounds are hypotheses here. -/
theorem coercive_quarter (F mass interaction head K δ : ℝ)
    (hmass : 0 ≤ mass) (hhead : head ≤ K)
    (hδ : δ ≤ 1 / 2) (hnorm : 0 ≤ interaction)
    (henergy : mass / 2 - (δ * mass + interaction * head) / 2 ≤ F) :
    mass / 4 - interaction * K / 2 ≤ F := by
  have hd := mul_le_mul_of_nonneg_right hδ hmass
  have hk := mul_le_mul_of_nonneg_left hhead hnorm
  nlinarith

/-- The polynomial inequality behind the summable hybrid D-majorant. -/
theorem complement_difference_bound (c d ρ σ : ℝ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hu : c ^ 2 + ρ = 1) (hv : d ^ 2 + σ = 1) :
    (c - d) ^ 2 ≤ 2 * (ρ + σ) := by
  have h1 : (1 - c) ^ 2 ≤ ρ := by nlinarith
  have h2 : (1 - d) ^ 2 ≤ σ := by nlinarith
  nlinarith [sq_nonneg ((1 - c) + (1 - d))]

/-- The written argument derives edge equality from equality of a nonnegative
series. This lemma propagates edge equality on an arbitrary index type,
including countably many band-frequency vertices. -/
theorem connected_phase_rigidity {ι : Type*}
    (E : ι → ι → Prop) (a b : ι → ℝ)
    (hconnected : ∀ i j, Relation.ReflTransGen E i j)
    (hedge : ∀ i j, E i j → a i = a j ∧ b i = b j) :
    ∀ i j, a i = a j ∧ b i = b j := by
  intro i j
  have hpath := hconnected i j
  induction hpath with
  | refl => exact ⟨rfl, rfl⟩
  | @tail j k _ hjk ih =>
    have he := hedge j k hjk
    exact ⟨ih.1.trans he.1, ih.2.trans he.2⟩

/-- Countable-graph version of the local equality mechanism, with a chosen
base vertex. The result is a single Cartesian U(1) phase. -/
theorem common_phase_arbitrary {ι : Type*} (i₀ : ι)
    (E : ι → ι → Prop) (a b : ι → ℝ)
    (hu : ∀ i, a i ^ 2 + b i ^ 2 = 1)
    (hconnected : ∀ i j, Relation.ReflTransGen E i j)
    (hedge : ∀ i j, E i j → a i = a j ∧ b i = b j) :
    ∃ a₀ b₀ : ℝ, a₀ ^ 2 + b₀ ^ 2 = 1 ∧ ∀ i, a i = a₀ ∧ b i = b₀ := by
  refine ⟨a i₀, b i₀, hu i₀, ?_⟩
  intro i
  exact connected_phase_rigidity E a b hconnected hedge i i₀

end Multiband.InfiniteCore
