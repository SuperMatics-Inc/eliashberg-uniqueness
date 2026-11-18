import Multiband.Density

noncomputable section
open scoped BigOperators

namespace Multiband

/-- The exact alignment loss in Cartesian coordinates of unit transverse phases. -/
def alignmentLoss {N : ℕ} (J : Fin N → Fin N → ℝ) (r a b : Density N) : ℝ :=
  (1 / 2 : ℝ) * ∑ n, ∑ m, J n m * r n * r m * (1 - (a n * a m + b n * b m))

theorem unit_phase_loss_nonneg (a b c d : ℝ)
    (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1) :
    0 ≤ 1 - (a * c + b * d) := by
  nlinarith [sq_nonneg (a - c), sq_nonneg (b - d)]

theorem unit_phase_loss_zero_iff (a b c d : ℝ)
    (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1) :
    1 - (a * c + b * d) = 0 ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hsq : (a - c) ^ 2 + (b - d) ^ 2 = 0 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (a - c), sq_nonneg (b - d)]
  · rintro ⟨rfl, rfl⟩
    nlinarith

theorem alignmentLoss_nonneg {N : ℕ} (J : Fin N → Fin N → ℝ) (r a b : Density N)
    (hJ : ∀ n m, 0 ≤ J n m) (hr : ∀ n, 0 ≤ r n)
    (hu : ∀ n, a n ^ 2 + b n ^ 2 = 1) : 0 ≤ alignmentLoss J r a b := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro n _
  apply Finset.sum_nonneg
  intro m _
  exact mul_nonneg (mul_nonneg (mul_nonneg (hJ n m) (hr n)) (hr m))
    (unit_phase_loss_nonneg _ _ _ _ (hu n) (hu m))

/-- Equality propagates along positive-coupling edges. -/
theorem alignmentLoss_edge_equality {N : ℕ} (J : Fin N → Fin N → ℝ) (r a b : Density N)
    (hJ : ∀ n m, 0 ≤ J n m) (hr : ∀ n, 0 < r n)
    (hu : ∀ n, a n ^ 2 + b n ^ 2 = 1) (hz : alignmentLoss J r a b = 0)
    {i j : Fin N} (hij : 0 < J i j) : a i = a j ∧ b i = b j := by
  have hnonneg (n m : Fin N) :
      0 ≤ J n m * r n * r m * (1 - (a n * a m + b n * b m)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (hJ n m) (hr n).le) (hr m).le)
      (unit_phase_loss_nonneg _ _ _ _ (hu n) (hu m))
  have hle : J i j * r i * r j * (1 - (a i * a j + b i * b j)) ≤
      ∑ n, ∑ m, J n m * r n * r m * (1 - (a n * a m + b n * b m)) := by
    calc
      _ ≤ ∑ m, J i m * r i * r m * (1 - (a i * a m + b i * b m)) :=
        Finset.single_le_sum (fun m _ => hnonneg i m) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum
        (fun n _ => Finset.sum_nonneg fun m _ => hnonneg n m) (Finset.mem_univ i)
  have hs : (∑ n, ∑ m, J n m * r n * r m * (1 - (a n * a m + b n * b m))) = 0 := by
    unfold alignmentLoss at hz
    linarith
  rw [hs] at hle
  have hp : 0 < J i j * r i * r j := mul_pos (mul_pos hij (hr i)) (hr j)
  have hl : 1 - (a i * a j + b i * b j) = 0 := by
    have := unit_phase_loss_nonneg _ _ _ _ (hu i) (hu j)
    nlinarith
  exact (unit_phase_loss_zero_iff _ _ _ _ (hu i) (hu j)).mp hl

/-- Connectedness plus positive support leaves exactly one U(1) phase. The U(1)
parameter is the unit Cartesian pair (a i,b i), so no branch of arg is chosen. -/
theorem common_phase_of_alignment_equality {N : ℕ}
    (J : Fin N → Fin N → ℝ) (r a b : Density N)
    (hJ : ∀ n m, 0 ≤ J n m) (hr : ∀ n, 0 < r n)
    (hu : ∀ n, a n ^ 2 + b n ^ 2 = 1)
    (hconnected : ∀ i j, Relation.ReflTransGen (fun n m => 0 < J n m) i j)
    (hz : alignmentLoss J r a b = 0) :
    ∀ i j, a i = a j ∧ b i = b j := by
  intro i j
  have hpath := hconnected i j
  induction hpath with
  | refl => exact ⟨rfl, rfl⟩
  | @tail j k _ hjk ih =>
    have he := alignmentLoss_edge_equality J r a b hJ hr hu hz hjk
    exact ⟨ih.1.trans he.1, ih.2.trans he.2⟩

/-- A single unit complex phase, represented without an arg branch. -/
theorem common_unit_phase {N : ℕ} (hN : 0 < N)
    (J : Fin N → Fin N → ℝ) (r a b : Density N)
    (hJ : ∀ n m, 0 ≤ J n m) (hr : ∀ n, 0 < r n)
    (hu : ∀ n, a n ^ 2 + b n ^ 2 = 1)
    (hconnected : ∀ i j, Relation.ReflTransGen (fun n m => 0 < J n m) i j)
    (hz : alignmentLoss J r a b = 0) :
    ∃ a₀ b₀ : ℝ, a₀ ^ 2 + b₀ ^ 2 = 1 ∧ ∀ n, a n = a₀ ∧ b n = b₀ := by
  let i : Fin N := ⟨0, hN⟩
  refine ⟨a i, b i, hu i, ?_⟩
  intro n
  exact common_phase_of_alignment_equality J r a b hJ hr hu hconnected hz n i

/-- In particular a non-common phase (including a nontrivial real pi pattern)
strictly increases the energy relative to aligned spins with the same amplitudes. -/
theorem noncommon_phase_strict_loss {N : ℕ}
    (J : Fin N → Fin N → ℝ) (r a b : Density N)
    (hJ : ∀ n m, 0 ≤ J n m) (hr : ∀ n, 0 < r n)
    (hu : ∀ n, a n ^ 2 + b n ^ 2 = 1)
    (hconnected : ∀ i j, Relation.ReflTransGen (fun n m => 0 < J n m) i j)
    (hexotic : ∃ i j, a i ≠ a j ∨ b i ≠ b j) : 0 < alignmentLoss J r a b := by
  have hn := alignmentLoss_nonneg J r a b hJ (fun n => (hr n).le) hu
  apply lt_of_le_of_ne hn
  intro he
  have hc := common_phase_of_alignment_equality J r a b hJ hr hu hconnected he.symm
  obtain ⟨i, j, hij⟩ := hexotic
  rcases hij with ha | hb
  · exact ha (hc i j).1
  · exact hb (hc i j).2

/-- Scalar fold remainder rigidity. The positive longitudinal amplitude is
essential; this is why the support lemma is needed before using equality. -/
theorem fold_site_rigidity (w c η k : ℝ) (hw : 0 < w) (hc : 0 < c)
    (hη : η = 1 ∨ η = -1) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hz : 2 * w * c * (1 - η * k) = 0) : η = 1 ∧ k = 1 := by
  have hp : 0 < 2 * w * c := by positivity
  have he : 1 - η * k = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  rcases hη with hη | hη
  · subst η
    constructor
    · rfl
    · nlinarith
  · subst η
    nlinarith

/-- Once the fold site loss vanishes, the paired longitudinal spins have the
correct strict signs. The symbols k,d are cos(delta),sin(delta). -/
theorem fold_equality_no_spin_flip (w c s η k d : ℝ)
    (hw : 0 < w) (hc : 0 < c) (hη : η = 1 ∨ η = -1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1) (hunit : k ^ 2 + d ^ 2 = 1)
    (hz : 2 * w * c * (1 - η * k) = 0) :
    0 < η * c * k + s * d ∧ η * c * k - s * d > 0 := by
  obtain ⟨hη', hk'⟩ := fold_site_rigidity w c η k hw hc hη hk hk1 hz
  have hd : d = 0 := by rw [hk'] at hunit; nlinarith [sq_nonneg d]
  simp only [hη', hk', hd, one_mul, mul_one, mul_zero, add_zero, sub_zero]
  exact ⟨hc, hc⟩

/-- The finite full-spin functional in Cartesian coordinates. Set J n n = 0
to implement the manuscript's excluded self interaction. -/
def spinEnergy {N : ℕ} (w ε : Density N) (J : Fin N → Fin N → ℝ)
    (x y z : Density N) : ℝ :=
  (∑ n, w n * (1 - ε n * z n)) + (1 / 2 : ℝ) * ∑ n, ∑ m,
    J n m * (ε n * ε m - (x n * x m + y n * y m + z n * z m))

/-- The alignment loss follows by subtracting the two full-spin energies. -/
theorem spin_alignment_identity {N : ℕ} (w ε : Density N)
    (J : Fin N → Fin N → ℝ) (r z a b : Density N) :
    spinEnergy w ε J (fun n => r n * a n) (fun n => r n * b n) z =
      spinEnergy w ε J r 0 z + alignmentLoss J r a b := by
  have hsum : (∑ n, ∑ m, J n m *
      (ε n * ε m - (r n * a n * (r m * a m) + r n * b n * (r m * b m) + z n * z m))) =
      (∑ n, ∑ m, J n m * (ε n * ε m - (r n * r m + 0 * 0 + z n * z m))) +
      (∑ n, ∑ m, J n m * r n * r m * (1 - (a n * a m + b n * b m))) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    ring
  unfold spinEnergy alignmentLoss
  simp only [Pi.zero_apply]
  rw [hsum]
  ring

/-- Both the original and aligned spins lie on the sphere under the displayed
radius hypotheses. Thus the alignment comparison uses admissible competitors. -/
theorem alignment_preserves_unit_spins {N : ℕ} (r z a b : Density N)
    (hu : ∀ n, a n ^ 2 + b n ^ 2 = 1)
    (hspin : ∀ n, r n ^ 2 + z n ^ 2 = 1) :
    (∀ n, (r n * a n) ^ 2 + (r n * b n) ^ 2 + z n ^ 2 = 1) ∧
      (∀ n, r n ^ 2 + (0 : ℝ) ^ 2 + z n ^ 2 = 1) := by
  constructor
  · intro n
    nlinarith [mul_nonneg (sq_nonneg (r n)) (sq_nonneg (a n)),
      mul_nonneg (sq_nonneg (r n)) (sq_nonneg (b n)), hu n, hspin n,
      congrArg (fun t : ℝ => r n ^ 2 * t) (hu n)]
  · simpa using hspin

/-- With positive transverse support and connectivity, a state with broken
time-reversal symmetry or nontrivial relative signs cannot minimize the
full-spin energy. The written proof supplies positivity at the minimizer. -/
theorem noncommon_spin_not_global_minimum {N : ℕ} (w ε : Density N)
    (J : Fin N → Fin N → ℝ) (r z a b : Density N)
    (hJ : ∀ n m, 0 ≤ J n m) (hr : ∀ n, 0 < r n)
    (hu : ∀ n, a n ^ 2 + b n ^ 2 = 1)
    (hspin : ∀ n, r n ^ 2 + z n ^ 2 = 1)
    (hconnected : ∀ i j, Relation.ReflTransGen (fun n m => 0 < J n m) i j)
    (hexotic : ∃ i j, a i ≠ a j ∨ b i ≠ b j) :
    ∃ x' y' z' : Density N,
      (∀ n, x' n ^ 2 + y' n ^ 2 + z' n ^ 2 = 1) ∧
      spinEnergy w ε J x' y' z' <
        spinEnergy w ε J (fun n => r n * a n) (fun n => r n * b n) z := by
  refine ⟨r, 0, z, ?_, ?_⟩
  · simpa using (alignment_preserves_unit_spins r z a b hu hspin).2
  · rw [spin_alignment_identity]
    have hpos := noncommon_phase_strict_loss J r a b hJ hr hu hconnected hexotic
    linarith

end Multiband
