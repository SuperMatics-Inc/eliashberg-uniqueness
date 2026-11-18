import Multiband.Density

noncomputable section

namespace Multiband

abbrev Vertex (p M : ℕ) := Fin p × Fin M

def sameCoupling {p M : ℕ} (dos : Fin p → ℝ) (lam : Fin p → Fin p → ℕ → ℝ)
    (u v : Vertex p M) : ℝ := dos u.1 * lam u.1 v.1 (Nat.dist u.2.val v.2.val)

def oppositeCoupling {p M : ℕ} (dos : Fin p → ℝ) (lam : Fin p → Fin p → ℕ → ℝ)
    (u v : Vertex p M) : ℝ := dos u.1 * lam u.1 v.1 (u.2.val + v.2.val + 1)

/-- Density-weighted reciprocity makes both coupling matrices symmetric. -/
theorem coupling_symmetry {p M : ℕ} (dos : Fin p → ℝ)
    (lam : Fin p → Fin p → ℕ → ℝ)
    (hrecip : ∀ a b k, dos a * lam a b k = dos b * lam b a k)
    (u v : Vertex p M) :
    sameCoupling dos lam u v = sameCoupling dos lam v u ∧
      oppositeCoupling dos lam u v = oppositeCoupling dos lam v u := by
  constructor
  · unfold sameCoupling
    rw [Nat.dist_comm]
    exact hrecip _ _ _
  · unfold oppositeCoupling
    rw [Nat.add_comm u.2.val v.2.val]
    exact hrecip _ _ _

/-- Distinct vertices in the same band have lag at least one, so intraband
monotonicity is needed only at positive lags, as in H2. -/
theorem offdiagonal_D_nonneg {p M : ℕ} (dos : Fin p → ℝ)
    (lam : Fin p → Fin p → ℕ → ℝ) (hdos : ∀ a, 0 < dos a)
    (hanti : ∀ a b j k, (a = b → 1 ≤ j) → j ≤ k → lam a b k ≤ lam a b j)
    {u v : Vertex p M} (hne : u ≠ v) :
    0 ≤ sameCoupling dos lam u v - oppositeCoupling dos lam u v := by
  have hj : u.1 = v.1 → 1 ≤ Nat.dist u.2.val v.2.val := by
    intro hab
    apply Nat.dist_pos_of_ne
    intro he
    apply hne
    exact Prod.ext hab (Fin.ext he)
  have hk : Nat.dist u.2.val v.2.val ≤ u.2.val + v.2.val + 1 := by
    unfold Nat.dist
    omega
  have hl := hanti u.1 v.1 _ _ hj hk
  unfold sameCoupling oppositeCoupling
  exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hl (hdos _).le)

theorem coupling_nonneg {p M : ℕ} (dos : Fin p → ℝ)
    (lam : Fin p → Fin p → ℕ → ℝ) (hdos : ∀ a, 0 < dos a)
    (hlam : ∀ a b k, 0 ≤ lam a b k) (u v : Vertex p M) :
    0 ≤ sameCoupling dos lam u v ∧ 0 ≤ oppositeCoupling dos lam u v :=
  ⟨mul_nonneg (hdos _).le (hlam _ _ _), mul_nonneg (hdos _).le (hlam _ _ _)⟩

/-- The Aase phonon model's dimensionless Einstein kernel. -/
def einstein (coupling varpi k : ℝ) : ℝ := coupling * varpi ^ 2 / (varpi ^ 2 + k ^ 2)

theorem einstein_pos (coupling varpi k : ℝ) (hc : 0 < coupling) (hv : 0 < varpi) :
    0 < einstein coupling varpi k := by
  unfold einstein
  exact div_pos (mul_pos hc (sq_pos_of_pos hv)) (by nlinarith [sq_nonneg k])

theorem einstein_antitone (coupling varpi j k : ℝ)
    (hc : 0 ≤ coupling) (hv : 0 < varpi) (hj : 0 ≤ j) (hjk : j ≤ k) :
    einstein coupling varpi k ≤ einstein coupling varpi j := by
  unfold einstein
  have hjd : 0 < varpi ^ 2 + j ^ 2 := by nlinarith [sq_nonneg j]
  have hkd : 0 < varpi ^ 2 + k ^ 2 := by nlinarith [sq_nonneg k]
  apply (div_le_div_iff₀ hkd hjd).mpr
  have hnum : 0 ≤ coupling * varpi ^ 2 := mul_nonneg hc (sq_nonneg _)
  have hsq : j ^ 2 ≤ k ^ 2 := by nlinarith
  nlinarith

theorem aase_coupling_pos (dos g omega : ℝ) (hdos : 0 < dos)
    (hg : g ≠ 0) (homega : 0 < omega) : 0 < 2 * dos * g ^ 2 / omega := by
  exact div_pos (mul_pos (mul_pos (by norm_num) hdos) (sq_pos_of_ne_zero hg)) homega

end Multiband
