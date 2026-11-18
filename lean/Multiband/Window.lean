import Multiband.Phase

noncomputable section
open scoped BigOperators

namespace Multiband
open KayThermo

/-- Full-spin reductions are explicit hypotheses, not postulated axioms. The paper
proves these by alignment and folding. This interface does NOT certify that those
maps have been constructed for the physical spin functional. -/
structure Reduction {N : ℕ} (C : Type*) (w L : Density N)
    (D W : Fin N → Fin N → ℝ) (energy : C → ℝ) where
  density : C → Density N
  inCube : ∀ S, density S ∈ cube N
  remainder : C → ℝ
  remainder_nonneg : ∀ S, 0 ≤ remainder S
  energy_eq : ∀ S, energy S = 2 * Gen w L D W (density S) + remainder S
  embed : Density N → C
  embed_density : ∀ ρ ∈ cube N, density (embed ρ) = ρ
  embed_remainder : ∀ ρ ∈ cube N, remainder (embed ρ) = 0

/-- Conditional version of Window(a,b): the minimizing density is constructed and
unique; precisely the zero-remainder configurations over it are global minima.
Interpreting this fiber as a U(1) orbit still requires support and equality cases. -/
theorem window_reduced_classification {N : ℕ} {C : Type*}
    (w L : Density N) (D W : Fin N → Fin N → ℝ) (energy : C → ℝ)
    (hw : ∀ n, 0 < w n) (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    (hW : ∀ n m, 0 ≤ W n m) (R : Reduction C w L D W energy) :
    ∃ ρ ∈ cube N, (∀ σ ∈ cube N, Gen w L D W ρ ≤ Gen w L D W σ) ∧
      ∀ S, (∀ S', energy S ≤ energy S') ↔ R.density S = ρ ∧ R.remainder S = 0 := by
  obtain ⟨ρ, ⟨hρ, hmin⟩, _⟩ := density_unique_minimum w L D W hw hD hW
  refine ⟨ρ, hρ, hmin, ?_⟩
  intro S
  constructor
  · intro hglobal
    have hembed : energy (R.embed ρ) = 2 * Gen w L D W ρ := by
      rw [R.energy_eq, R.embed_density ρ hρ, R.embed_remainder ρ hρ, add_zero]
    have hle := hglobal (R.embed ρ)
    rw [hembed, R.energy_eq] at hle
    have hd := hmin (R.density S) (R.inCube S)
    have hr := R.remainder_nonneg S
    have he : Gen w L D W (R.density S) = Gen w L D W ρ := by linarith
    have hds : R.density S = ρ := by
      apply Gen_min_unique w L D W hw hD hW (R.inCube S) hρ
      · intro σ hσ
        rw [he]
        exact hmin σ hσ
      · exact hmin
    exact ⟨hds, by linarith⟩
  · rintro ⟨hd, hr⟩ S'
    rw [R.energy_eq, R.energy_eq, hd, hr]
    have hmin' := hmin (R.density S') (R.inCube S')
    have hrem := R.remainder_nonneg S'
    linarith

/-- Strict exclusion of every configuration outside the equality fiber. -/
theorem outside_fiber_strict_energy {N : ℕ} {C : Type*}
    (w L : Density N) (D W : Fin N → Fin N → ℝ) (energy : C → ℝ)
    (hw : ∀ n, 0 < w n) (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    (hW : ∀ n m, 0 ≤ W n m) (R : Reduction C w L D W energy)
    {ρ : Density N} (hρ : ρ ∈ cube N)
    (hmin : ∀ σ ∈ cube N, Gen w L D W ρ ≤ Gen w L D W σ)
    {S : C} (hout : R.density S ≠ ρ ∨ R.remainder S ≠ 0) :
    energy (R.embed ρ) < energy S := by
  have hembed : energy (R.embed ρ) = 2 * Gen w L D W ρ := by
    rw [R.energy_eq, R.embed_density ρ hρ, R.embed_remainder ρ hρ, add_zero]
  have hmin' := hmin (R.density S) (R.inCube S)
  have hr := R.remainder_nonneg S
  have hle : energy (R.embed ρ) ≤ energy S := by rw [hembed, R.energy_eq]; linarith
  apply lt_of_le_of_ne hle
  intro he
  have heF : Gen w L D W (R.density S) = Gen w L D W ρ := by
    rw [hembed, R.energy_eq] at he
    linarith
  have hd : R.density S = ρ := by
    apply Gen_min_unique w L D W hw hD hW (R.inCube S) hρ
    · intro σ hσ
      rw [heF]
      exact hmin σ hσ
    · exact hmin
  have hz : R.remainder S = 0 := by
    rw [hembed, R.energy_eq, hd] at he
    linarith
  rcases hout with h | h
  · exact h hd
  · exact h hz

/-- Conditional Tc equality as SETS, not a single-crossing theorem. The outstanding
analytic input is descent from a negative quadratic direction. Reduction of the
full spin energy is separately explicit in R. -/
theorem instability_sets_equal {N : ℕ} {C Θ : Type*}
    (w L : Θ → Density N) (D W : Θ → Fin N → Fin N → ℝ)
    (energy : Θ → C → ℝ)
    (hw : ∀ T n, 0 < w T n)
    (hD : ∀ T n m, n ≠ m → 0 ≤ D T n m)
    (R : ∀ T, Reduction C (w T) (L T) (D T) (W T) (energy T))
    (descent : ∀ T, (∃ y, qForm (w T) (L T) (W T) y < 0) →
      ∃ ρ ∈ cube N, Gen (w T) (L T) (D T) (W T) ρ < 0) :
    {T | ∃ S, energy T S < 0} = {T | ∃ y, qForm (w T) (L T) (W T) y < 0} := by
  ext T
  constructor
  · rintro ⟨S, hS⟩
    apply negative_density_implies_negative_quadratic (w T) (L T) (D T) (W T)
      (hw T) (hD T) ((R T).inCube S)
    have hr := (R T).remainder_nonneg S
    rw [(R T).energy_eq] at hS
    linarith
  · intro hQ
    obtain ⟨ρ, hρ, hneg⟩ := descent T hQ
    refine ⟨(R T).embed ρ, ?_⟩
    rw [(R T).energy_eq, (R T).embed_density ρ hρ, (R T).embed_remainder ρ hρ]
    linarith

/-- The standard linear-gap diagonal correction cancels exactly in its stability
matrix. Spectral congruence and positivity of the conventional normal Z weights
remain external to this algebraic identity. -/
theorem linear_gap_matrix_bridge {N : ℕ} (d e : Density N)
    (W : Fin N → Fin N → ℝ) (i j : Fin N) :
    (if i = j then d i + e i else 0) - (W i j + if i = j then e i else 0) =
      (if i = j then d i else 0) - W i j := by
  split_ifs <;> ring

/-- Exact-rational checks of the outward displayed Arb GAP intervals. These do not
check the Krawczyk root boxes or the generation of the enclosure itself. -/
theorem aase_hard_gap_lower_positive :
    (0 : ℝ) < 0.00000367139685705 - 0.00000000000000000519 := by norm_num

theorem aase_frozen_gap_lower_positive :
    (0 : ℝ) < 0.00000366704952964 - 0.00000000000000000149 := by norm_num

theorem aase_hard_order {Eplus Epi : ℝ}
    (henclosure : Epi - Eplus ∈ Set.Icc
      (0.00000367139685705 - 0.00000000000000000519)
      (0.00000367139685705 + 0.00000000000000000519)) : Eplus < Epi := by
  have := aase_hard_gap_lower_positive
  linarith [henclosure.1]

theorem aase_frozen_order {Eplus Epi : ℝ}
    (henclosure : Epi - Eplus ∈ Set.Icc
      (0.00000366704952964 - 0.00000000000000000149)
      (0.00000366704952964 + 0.00000000000000000149)) : Eplus < Epi := by
  have := aase_frozen_gap_lower_positive
  linarith [henclosure.1]

/-- Independent exact arithmetic on the two displayed hard-cutoff energy boxes. -/
theorem aase_hard_energy_intervals_order {Eplus Epi : ℝ}
    (hplus : Eplus ∈ Set.Icc
      (-75.236285293566757956 - 0.000000000000000000314)
      (-75.236285293566757956 + 0.000000000000000000314))
    (hpi : Epi ∈ Set.Icc
      (-75.236281622169900901 - 0.000000000000000000347)
      (-75.236281622169900901 + 0.000000000000000000347)) : Eplus < Epi := by
  linarith [hplus.2, hpi.1]

/-- Independent exact arithmetic on the two displayed pinned-exterior energy boxes. -/
theorem aase_frozen_energy_intervals_order {Eplus Epi : ℝ}
    (hplus : Eplus ∈ Set.Icc
      (-75.120037066569992192 - 0.000000000000000000295)
      (-75.120037066569992192 + 0.000000000000000000295))
    (hpi : Epi ∈ Set.Icc
      (-75.120033399520462553 - 0.000000000000000000683)
      (-75.120033399520462553 + 0.000000000000000000683)) : Eplus < Epi := by
  linarith [hplus.2, hpi.1]

end Multiband
