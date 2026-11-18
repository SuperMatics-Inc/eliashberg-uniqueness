import Multiband.Density

/-!
Finite/algebraic core only. The measurable irreducibility, compact-operator,
weak lower semicontinuity, and integral arguments in THEOREM.md are NOT
formalized here. The imported finite core is copied unchanged from the
multiband source identified in RIGOR.md.
-/

noncomputable section
namespace FSUniq

/-- The pointwise complement-square identity also applies to equal-frequency,
distinct-angle pairs. There is no index inequality hypothesis. -/
theorem complement_identity (s c t d : ℝ)
    (h : s ^ 2 + c ^ 2 = 1) (h' : t ^ 2 + d ^ 2 = 1) :
    1 - c * d = (s ^ 2 + t ^ 2 + (c - d) ^ 2) / 2 := by
  nlinarith [h, h']

/-- The scalar normal-state remainder is an exact square. -/
theorem normal_remainder (r c : ℝ) (h : c ^ 2 = 1 - r) :
    1 - c = r / 2 + (1 - c) ^ 2 / 2 := by
  nlinarith [h]

/-- Real-coordinate phase mismatch equals half a squared chord. -/
theorem phase_chord (a b c d : ℝ)
    (hu : a ^ 2 + b ^ 2 = 1) (hv : c ^ 2 + d ^ 2 = 1) :
    1 - (a * c + b * d) = ((a - c) ^ 2 + (b - d) ^ 2) / 2 := by
  nlinarith [hu, hv]

/-- At a positive-weight pair, zero alignment loss forces equal phases. -/
theorem positive_weight_phase_rigidity (p a b c d : ℝ) (hp : 0 < p)
    (hu : a ^ 2 + b ^ 2 = 1) (hv : c ^ 2 + d ^ 2 = 1)
    (hz : p * (1 - (a * c + b * d)) = 0) : a = c ∧ b = d := by
  have hd : 1 - (a * c + b * d) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  have hc := phase_chord a b c d hu hv
  have ha : (a - c) ^ 2 = 0 := by nlinarith [sq_nonneg (b - d)]
  have hb : (b - d) ^ 2 = 0 := by nlinarith [sq_nonneg (a - c)]
  constructor <;> nlinarith

/-- Saturating the positive complement cannot increase a D-pair penalty. -/
theorem complement_saturation (c d C D : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hC : c ≤ C) (hD : d ≤ D) :
    1 - C * D ≤ 1 - c * d := by
  have hstep := mul_le_mul hC hD hd (le_trans hc hC)
  linarith

/-- The midpoint coefficient used to force strong convergence of minimizing
sequences is purely algebraic once strong convexity is established. -/
theorem midpoint_gap (a b m q : ℝ)
    (hmin : a ≤ m) (hconv : m ≤ (a + b) / 2 - q / 32) :
    q / 16 ≤ b - a := by
  linarith

#print axioms complement_identity
#print axioms normal_remainder
#print axioms phase_chord
#print axioms positive_weight_phase_rigidity
#print axioms complement_saturation
#print axioms midpoint_gap
#print axioms Multiband.hidden_substitution
#print axioms Multiband.density_unique_minimum
#print axioms Multiband.density_decomposition
#print axioms Multiband.normal_strict_minimum
#print axioms Multiband.negative_density_implies_negative_quadratic

end FSUniq
