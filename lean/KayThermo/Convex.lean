import Mathlib

noncomputable section

open scoped BigOperators

namespace KayThermo

/-- The closed density cube. -/
def cube (N : ℕ) : Set (Fin N → ℝ) := {ρ | ∀ n, ρ n ∈ Set.Icc (0 : ℝ) 1}

/-- The density functional with arbitrary coefficient arrays. -/
def Gen {N : ℕ} (w L : Fin N → ℝ) (D W : Fin N → Fin N → ℝ)
    (ρ : Fin N → ℝ) : ℝ :=
  (∑ n, w n * (1 - Real.sqrt (1 - ρ n))) + (∑ n, L n * ρ n) +
  (1 / 4 : ℝ) * (∑ n, ∑ m, if n ≠ m then D n m *
    (Real.sqrt (1 - ρ n) - Real.sqrt (1 - ρ m)) ^ 2 else 0) -
  (1 / 2 : ℝ) * (∑ n, ∑ m, W n m * Real.sqrt (ρ n * ρ m))

private theorem geom_mid (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (Real.sqrt (a * b) + Real.sqrt (c * d)) / 2 ≤
      Real.sqrt (((a + c) / 2) * ((b + d) / 2)) := by
  have hs1 := Real.sq_sqrt ha
  have hs2 := Real.sq_sqrt hb
  have hs3 := Real.sq_sqrt hc
  have hs4 := Real.sq_sqrt hd
  have hn1 := Real.sqrt_nonneg a
  have hn2 := Real.sqrt_nonneg b
  have hn3 := Real.sqrt_nonneg c
  have hn4 := Real.sqrt_nonneg d
  rw [Real.sqrt_mul ha, Real.sqrt_mul hc]
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  have h := sq_nonneg (Real.sqrt a * Real.sqrt d - Real.sqrt c * Real.sqrt b)
  nlinarith [mul_self_nonneg (Real.sqrt a * Real.sqrt b),
    mul_self_nonneg (Real.sqrt c * Real.sqrt d)]

private theorem sqrt_mid (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a + Real.sqrt b) / 2 ≤ Real.sqrt ((a + b) / 2) := by
  have h := Real.strictConcaveOn_sqrt.concaveOn.2 (show a ∈ Set.Ici (0 : ℝ) from ha)
    (show b ∈ Set.Ici (0 : ℝ) from hb) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  convert h using 1 <;> congr 1 <;> ring

private theorem sqrt_mid_strict (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) :
    (Real.sqrt a + Real.sqrt b) / 2 < Real.sqrt ((a + b) / 2) := by
  have h := Real.strictConcaveOn_sqrt.2 (show a ∈ Set.Ici (0 : ℝ) from ha)
    (show b ∈ Set.Ici (0 : ℝ) from hb) hab (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  convert h using 1 <;> congr 1 <;> ring

private theorem diff_mid (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (Real.sqrt ((a+c)/2) - Real.sqrt ((b+d)/2))^2 ≤
    ((Real.sqrt a - Real.sqrt b)^2 + (Real.sqrt c - Real.sqrt d)^2)/2 := by
  have h := geom_mid a b c d ha hb hc hd
  rw [Real.sqrt_mul ha, Real.sqrt_mul hc,
    Real.sqrt_mul (by linarith : 0 ≤ (a + c) / 2)] at h
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt hc
  have h4 := Real.sq_sqrt hd
  have h5 := Real.sq_sqrt (show 0 ≤ (a+c)/2 by linarith)
  have h6 := Real.sq_sqrt (show 0 ≤ (b+d)/2 by linarith)
  nlinarith

/-- Midpoint convexity, strict unless the two density vectors coincide. -/
theorem Gen_midpoint {N : ℕ} (w L : Fin N → ℝ) (D W : Fin N → Fin N → ℝ)
    (hw : ∀ n, 0 < w n) (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    (hW : ∀ n m, 0 ≤ W n m) {ρ σ : Fin N → ℝ}
    (hρ : ρ ∈ cube N) (hσ : σ ∈ cube N) :
    Gen w L D W (fun n => (ρ n + σ n) / 2) ≤
      (Gen w L D W ρ + Gen w L D W σ) / 2 ∧
    (ρ ≠ σ → Gen w L D W (fun n => (ρ n + σ n) / 2) <
      (Gen w L D W ρ + Gen w L D W σ) / 2) := by
  have hfirst (n : Fin N) :
      w n * (1 - Real.sqrt (1 - (ρ n + σ n) / 2)) ≤
      (w n * (1 - Real.sqrt (1 - ρ n)) +
       w n * (1 - Real.sqrt (1 - σ n))) / 2 := by
    have h := sqrt_mid (1 - ρ n) (1 - σ n)
      (by have := (hρ n).2; linarith) (by have := (hσ n).2; linarith)
    have : 1 - (ρ n + σ n) / 2 = ((1 - ρ n) + (1 - σ n)) / 2 := by ring
    rw [this]
    nlinarith [hw n]
  have hfirst_strict (n : Fin N) (hn : ρ n ≠ σ n) :
      w n * (1 - Real.sqrt (1 - (ρ n + σ n) / 2)) <
      (w n * (1 - Real.sqrt (1 - ρ n)) +
       w n * (1 - Real.sqrt (1 - σ n))) / 2 := by
    have h := sqrt_mid_strict (1 - ρ n) (1 - σ n)
      (by have := (hρ n).2; linarith) (by have := (hσ n).2; linarith)
      (by intro he; apply hn; linarith)
    have : 1 - (ρ n + σ n) / 2 = ((1 - ρ n) + (1 - σ n)) / 2 := by ring
    rw [this]
    nlinarith [hw n]
  have hsfirst :
      (∑ n, w n * (1 - Real.sqrt (1 - (ρ n + σ n) / 2))) ≤
      ((∑ n, w n * (1 - Real.sqrt (1 - ρ n))) +
       (∑ n, w n * (1 - Real.sqrt (1 - σ n)))) / 2 := by
    have h := Finset.sum_le_sum fun n (_ : n ∈ Finset.univ) => hfirst n
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib] at h
    exact h
  have hsfirst_strict (hne : ρ ≠ σ) :
      (∑ n, w n * (1 - Real.sqrt (1 - (ρ n + σ n) / 2))) <
      ((∑ n, w n * (1 - Real.sqrt (1 - ρ n))) +
       (∑ n, w n * (1 - Real.sqrt (1 - σ n)))) / 2 := by
    have hex : ∃ n, ρ n ≠ σ n := by
      by_contra h
      apply hne
      funext n
      push Not at h
      exact h n
    obtain ⟨n, hn⟩ := hex
    have h := Finset.sum_lt_sum (fun i (_ : i ∈ Finset.univ) => hfirst i)
      ⟨n, Finset.mem_univ n, hfirst_strict n hn⟩
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib] at h
    exact h
  have hslinear :
      (∑ n, L n * ((ρ n + σ n) / 2)) =
      ((∑ n, L n * ρ n) + (∑ n, L n * σ n)) / 2 := by
    simp only [mul_div, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
  have hpair (n m : Fin N) :
      (if n ≠ m then D n m *
        (Real.sqrt (1 - (ρ n + σ n)/2) - Real.sqrt (1 - (ρ m + σ m)/2))^2 else 0) ≤
      ((if n ≠ m then D n m * (Real.sqrt (1 - ρ n) - Real.sqrt (1 - ρ m))^2 else 0) +
       (if n ≠ m then D n m * (Real.sqrt (1 - σ n) - Real.sqrt (1 - σ m))^2 else 0)) / 2 := by
    split_ifs with hnm
    · have h := diff_mid (1-ρ n) (1-ρ m) (1-σ n) (1-σ m)
        (by have := (hρ n).2; linarith) (by have := (hρ m).2; linarith)
        (by have := (hσ n).2; linarith) (by have := (hσ m).2; linarith)
      have hn : 1 - (ρ n + σ n)/2 = ((1-ρ n)+(1-σ n))/2 := by ring
      have hm : 1 - (ρ m + σ m)/2 = ((1-ρ m)+(1-σ m))/2 := by ring
      rw [hn, hm]
      nlinarith [hD n m hnm]
    · norm_num
  have hspair :
      (∑ n, ∑ m, if n ≠ m then D n m *
        (Real.sqrt (1 - (ρ n + σ n)/2) - Real.sqrt (1 - (ρ m + σ m)/2))^2 else 0) ≤
      ((∑ n, ∑ m, if n ≠ m then D n m * (Real.sqrt (1 - ρ n) - Real.sqrt (1 - ρ m))^2 else 0) +
       (∑ n, ∑ m, if n ≠ m then D n m * (Real.sqrt (1 - σ n) - Real.sqrt (1 - σ m))^2 else 0)) / 2 := by
    have h := Finset.sum_le_sum fun n (_ : n ∈ Finset.univ) =>
      Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hpair n m
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib] at h
    exact h
  have hgeom (n m : Fin N) :
      (W n m * Real.sqrt (ρ n * ρ m) + W n m * Real.sqrt (σ n * σ m)) / 2 ≤
      W n m * Real.sqrt (((ρ n + σ n)/2) * ((ρ m + σ m)/2)) := by
    have h := geom_mid (ρ n) (ρ m) (σ n) (σ m)
      (hρ n).1 (hρ m).1 (hσ n).1 (hσ m).1
    nlinarith [hW n m]
  have hsgeom :
      ((∑ n, ∑ m, W n m * Real.sqrt (ρ n * ρ m)) +
       (∑ n, ∑ m, W n m * Real.sqrt (σ n * σ m))) / 2 ≤
      (∑ n, ∑ m, W n m * Real.sqrt (((ρ n + σ n)/2) * ((ρ m + σ m)/2))) := by
    have h := Finset.sum_le_sum fun n (_ : n ∈ Finset.univ) =>
      Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hgeom n m
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib] at h
    exact h
  constructor
  · simp only [Gen]; linarith
  · intro hne
    have hs := hsfirst_strict hne
    simp only [Gen]; linarith

private theorem gen_sqrt_scaled_product (k x y : ℝ) (hk : 0 ≤ k) :
    Real.sqrt ((k * x) * (k * y)) = k * Real.sqrt (x * y) := by
  calc
    Real.sqrt ((k * x) * (k * y)) = Real.sqrt (k ^ 2 * (x * y)) := by
      congr 1
      ring
    _ = Real.sqrt (k ^ 2) * Real.sqrt (x * y) := Real.sqrt_mul (sq_nonneg k) _
    _ = k * Real.sqrt (x * y) := by rw [Real.sqrt_sq hk]

private theorem gen_two_term_cauchy (p q r s : ℝ) :
    (p * q + r * s) ^ 2 ≤ (p ^ 2 + r ^ 2) * (q ^ 2 + s ^ 2) := by
  nlinarith only [sq_nonneg (p * s - r * q)]

/-- The geometric mean is concave for arbitrary nonnegative weights. -/
private theorem gen_geom_weighted (x y z t a b : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * Real.sqrt (x * y) + b * Real.sqrt (z * t) ≤
      Real.sqrt ((a * x + b * z) * (a * y + b * t)) := by
  have hprod_a : Real.sqrt (a * x) * Real.sqrt (a * y) =
      a * Real.sqrt (x * y) := by
    rw [← Real.sqrt_mul (mul_nonneg ha hx), gen_sqrt_scaled_product a x y ha]
  have hprod_b : Real.sqrt (b * z) * Real.sqrt (b * t) =
      b * Real.sqrt (z * t) := by
    rw [← Real.sqrt_mul (mul_nonneg hb hz), gen_sqrt_scaled_product b z t hb]
  have h := gen_two_term_cauchy (Real.sqrt (a * x)) (Real.sqrt (a * y))
    (Real.sqrt (b * z)) (Real.sqrt (b * t))
  rw [hprod_a, hprod_b, Real.sq_sqrt (mul_nonneg ha hx),
    Real.sq_sqrt (mul_nonneg hb hz), Real.sq_sqrt (mul_nonneg ha hy),
    Real.sq_sqrt (mul_nonneg hb ht)] at h
  exact (Real.le_sqrt (by positivity) (by positivity)).2 h

private theorem gen_sqrt_diff_sq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 = x + y - 2 * Real.sqrt (x * y) := by
  rw [sub_sq, Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_mul hx]
  ring

private theorem gen_diff_weighted (x y z t a b : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt (a * x + b * z) - Real.sqrt (a * y + b * t)) ^ 2 ≤
      a * (Real.sqrt x - Real.sqrt y) ^ 2 +
      b * (Real.sqrt z - Real.sqrt t) ^ 2 := by
  rw [gen_sqrt_diff_sq _ _ (by positivity) (by positivity),
    gen_sqrt_diff_sq x y hx hy, gen_sqrt_diff_sq z t hz ht]
  nlinarith only [gen_geom_weighted x y z t a b hx hy hz ht ha hb]

private theorem gen_sqrt_loss_weighted (x y a b : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    1 - Real.sqrt (a * x + b * y) ≤
      a * (1 - Real.sqrt x) + b * (1 - Real.sqrt y) := by
  have h := Real.strictConcaveOn_sqrt.concaveOn.2
    (show x ∈ Set.Ici (0 : ℝ) from hx) (show y ∈ Set.Ici (0 : ℝ) from hy)
    ha hb hab
  simp only [smul_eq_mul] at h
  linarith

private theorem gen_sqrt_loss_weighted_strict (x y a b : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    1 - Real.sqrt (a * x + b * y) <
      a * (1 - Real.sqrt x) + b * (1 - Real.sqrt y) := by
  have h := Real.strictConcaveOn_sqrt.2
    (show x ∈ Set.Ici (0 : ℝ) from hx) (show y ∈ Set.Ici (0 : ℝ) from hy)
    hxy ha hb hab
  simp only [smul_eq_mul] at h
  linarith

private theorem gen_cube_convex (N : ℕ) : Convex ℝ (cube N) := by
  intro ρ hρ σ hσ a b ha hb hab n
  constructor
  · change 0 ≤ a * ρ n + b * σ n
    exact add_nonneg (mul_nonneg ha (hρ n).1) (mul_nonneg hb (hσ n).1)
  · change a * ρ n + b * σ n ≤ 1
    calc
      a * ρ n + b * σ n ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left (hρ n).2 ha)
          (mul_le_mul_of_nonneg_left (hσ n).2 hb)
      _ = 1 := by simpa using hab

/-- Weighted convexity, with strictness for distinct densities and positive weights. -/
private theorem Gen_weighted_general {N : ℕ} (w L : Fin N → ℝ)
    (D W : Fin N → Fin N → ℝ)
    (hw : ∀ n, 0 < w n) (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    (hW : ∀ n m, 0 ≤ W n m) {ρ σ : Fin N → ℝ}
    (hρ : ρ ∈ cube N) (hσ : σ ∈ cube N) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Gen w L D W (fun n => a * ρ n + b * σ n) ≤
      a * Gen w L D W ρ + b * Gen w L D W σ ∧
    (ρ ≠ σ → 0 < a → 0 < b →
      Gen w L D W (fun n => a * ρ n + b * σ n) <
        a * Gen w L D W ρ + b * Gen w L D W σ) := by
  have hcompl (n : Fin N) :
      1 - (a * ρ n + b * σ n) = a * (1 - ρ n) + b * (1 - σ n) := by
    linarith
  have hfirst (n : Fin N) :
      w n * (1 - Real.sqrt (1 - (a * ρ n + b * σ n))) ≤
      a * (w n * (1 - Real.sqrt (1 - ρ n))) +
      b * (w n * (1 - Real.sqrt (1 - σ n))) := by
    have h := mul_le_mul_of_nonneg_left
      (gen_sqrt_loss_weighted (1 - ρ n) (1 - σ n) a b
        (by have := (hρ n).2; linarith) (by have := (hσ n).2; linarith)
        ha hb hab) (hw n).le
    rw [← hcompl n] at h
    convert h using 1 <;> ring
  have hfirst_strict (n : Fin N) (hn : ρ n ≠ σ n) (ha' : 0 < a) (hb' : 0 < b) :
      w n * (1 - Real.sqrt (1 - (a * ρ n + b * σ n))) <
      a * (w n * (1 - Real.sqrt (1 - ρ n))) +
      b * (w n * (1 - Real.sqrt (1 - σ n))) := by
    have h := mul_lt_mul_of_pos_left
      (gen_sqrt_loss_weighted_strict (1 - ρ n) (1 - σ n) a b
        (by have := (hρ n).2; linarith) (by have := (hσ n).2; linarith)
        (by intro he; apply hn; linarith) ha' hb' hab) (hw n)
    rw [← hcompl n] at h
    convert h using 1 <;> ring
  have hsfirst :
      (∑ n, w n * (1 - Real.sqrt (1 - (a * ρ n + b * σ n)))) ≤
      a * (∑ n, w n * (1 - Real.sqrt (1 - ρ n))) +
      b * (∑ n, w n * (1 - Real.sqrt (1 - σ n))) := by
    have h := Finset.sum_le_sum fun n (_ : n ∈ Finset.univ) => hfirst n
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h
  have hsfirst_strict (hne : ρ ≠ σ) (ha' : 0 < a) (hb' : 0 < b) :
      (∑ n, w n * (1 - Real.sqrt (1 - (a * ρ n + b * σ n)))) <
      a * (∑ n, w n * (1 - Real.sqrt (1 - ρ n))) +
      b * (∑ n, w n * (1 - Real.sqrt (1 - σ n))) := by
    have hex : ∃ n, ρ n ≠ σ n := by
      by_contra h
      apply hne
      funext n
      push Not at h
      exact h n
    obtain ⟨n, hn⟩ := hex
    have h := Finset.sum_lt_sum (fun i (_ : i ∈ Finset.univ) => hfirst i)
      ⟨n, Finset.mem_univ n, hfirst_strict n hn ha' hb'⟩
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h
  have hslinear :
      (∑ n, L n * (a * ρ n + b * σ n)) =
      a * (∑ n, L n * ρ n) + b * (∑ n, L n * σ n) := by
    calc
      (∑ n, L n * (a * ρ n + b * σ n)) =
          ∑ n, (a * (L n * ρ n) + b * (L n * σ n)) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hpair (n m : Fin N) :
      (if n ≠ m then D n m *
        (Real.sqrt (1 - (a * ρ n + b * σ n)) -
         Real.sqrt (1 - (a * ρ m + b * σ m))) ^ 2 else 0) ≤
      a * (if n ≠ m then D n m *
        (Real.sqrt (1 - ρ n) - Real.sqrt (1 - ρ m)) ^ 2 else 0) +
      b * (if n ≠ m then D n m *
        (Real.sqrt (1 - σ n) - Real.sqrt (1 - σ m)) ^ 2 else 0) := by
    split_ifs with hnm
    · have h := mul_le_mul_of_nonneg_left
        (gen_diff_weighted (1 - ρ n) (1 - ρ m) (1 - σ n) (1 - σ m) a b
          (by have := (hρ n).2; linarith) (by have := (hρ m).2; linarith)
          (by have := (hσ n).2; linarith) (by have := (hσ m).2; linarith)
          ha hb) (hD n m hnm)
      rw [← hcompl n, ← hcompl m] at h
      convert h using 1 <;> ring
    · norm_num
  have hspair :
      (∑ n, ∑ m, if n ≠ m then D n m *
        (Real.sqrt (1 - (a * ρ n + b * σ n)) -
         Real.sqrt (1 - (a * ρ m + b * σ m))) ^ 2 else 0) ≤
      a * (∑ n, ∑ m, if n ≠ m then D n m *
        (Real.sqrt (1 - ρ n) - Real.sqrt (1 - ρ m)) ^ 2 else 0) +
      b * (∑ n, ∑ m, if n ≠ m then D n m *
        (Real.sqrt (1 - σ n) - Real.sqrt (1 - σ m)) ^ 2 else 0) := by
    have h := Finset.sum_le_sum fun n (_ : n ∈ Finset.univ) =>
      Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hpair n m
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h
  have hgeom (n m : Fin N) :
      a * (W n m * Real.sqrt (ρ n * ρ m)) +
      b * (W n m * Real.sqrt (σ n * σ m)) ≤
      W n m * Real.sqrt ((a * ρ n + b * σ n) * (a * ρ m + b * σ m)) := by
    have h := mul_le_mul_of_nonneg_left
      (gen_geom_weighted (ρ n) (ρ m) (σ n) (σ m) a b
        (hρ n).1 (hρ m).1 (hσ n).1 (hσ m).1 ha hb) (hW n m)
    convert h using 1 <;> ring
  have hsgeom :
      a * (∑ n, ∑ m, W n m * Real.sqrt (ρ n * ρ m)) +
      b * (∑ n, ∑ m, W n m * Real.sqrt (σ n * σ m)) ≤
      (∑ n, ∑ m, W n m *
        Real.sqrt ((a * ρ n + b * σ n) * (a * ρ m + b * σ m))) := by
    have h := Finset.sum_le_sum fun n (_ : n ∈ Finset.univ) =>
      Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hgeom n m
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using h
  constructor
  · simp only [Gen]
    linarith
  · intro hne ha' hb'
    have hs := hsfirst_strict hne ha' hb'
    simp only [Gen]
    linarith

/-- The density functional is convex on the closed density cube. -/
theorem Gen_convexOn {N : ℕ} (w L : Fin N → ℝ) (D W : Fin N → Fin N → ℝ)
    (hw : ∀ n, 0 < w n) (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    (hW : ∀ n m, 0 ≤ W n m) : ConvexOn ℝ (cube N) (Gen w L D W) := by
  refine ⟨gen_cube_convex N, ?_⟩
  intro ρ hρ σ hσ a b ha hb hab
  change Gen w L D W (a • ρ + b • σ) ≤ a * Gen w L D W ρ + b * Gen w L D W σ
  have heq : a • ρ + b • σ = fun n => a * ρ n + b * σ n := by
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact (Gen_weighted_general w L D W hw hD hW hρ hσ ha hb hab).1

/-- Positive one-body weights make the density functional strictly convex on the cube. -/
theorem Gen_strictConvexOn {N : ℕ} (w L : Fin N → ℝ) (D W : Fin N → Fin N → ℝ)
    (hw : ∀ n, 0 < w n) (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    (hW : ∀ n m, 0 ≤ W n m) : StrictConvexOn ℝ (cube N) (Gen w L D W) := by
  refine ⟨gen_cube_convex N, ?_⟩
  intro ρ hρ σ hσ hne a b ha hb hab
  change Gen w L D W (a • ρ + b • σ) < a * Gen w L D W ρ + b * Gen w L D W σ
  have heq : a • ρ + b • σ = fun n => a * ρ n + b * σ n := by
    funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact (Gen_weighted_general w L D W hw hD hW hρ hσ ha.le hb.le hab).2 hne ha hb

/-- The density cube is compact, including the zero-dimensional case. -/
theorem cube_isCompact (N : ℕ) : IsCompact (cube N) :=
  isCompact_pi_infinite (fun _ => isCompact_Icc)

/-- The general density functional is continuous even outside the cube. -/
theorem Gen_continuous {N : ℕ} (w L : Fin N → ℝ) (D W : Fin N → Fin N → ℝ) :
    Continuous (Gen w L D W) := by
  have hp : Continuous (fun ρ : Fin N → ℝ =>
      ∑ n, ∑ m, if n ≠ m then D n m *
        (Real.sqrt (1 - ρ n) - Real.sqrt (1 - ρ m)) ^ 2 else 0) := by
    refine continuous_finsetSum _ fun n _ => continuous_finsetSum _ fun m _ => ?_
    split_ifs <;> fun_prop
  unfold Gen
  apply Continuous.sub
  · apply Continuous.add
    · fun_prop
    · exact continuous_const.mul hp
  · fun_prop

/-- A minimum exists for arbitrary coefficients, independently of their signs. -/
theorem Gen_exists_min {N : ℕ} (w L : Fin N → ℝ) (D W : Fin N → Fin N → ℝ) :
    ∃ ρ ∈ cube N, ∀ σ ∈ cube N, Gen w L D W ρ ≤ Gen w L D W σ := by
  have hne : (cube N).Nonempty := ⟨0, fun _ => ⟨le_refl 0, zero_le_one⟩⟩
  exact (cube_isCompact N).exists_isMinOn hne (Gen_continuous w L D W).continuousOn

/-- Under the sign hypotheses, two minimizers of the density functional coincide. -/
theorem Gen_min_unique {N : ℕ} (w L : Fin N → ℝ) (D W : Fin N → Fin N → ℝ)
    (hw : ∀ n, 0 < w n) (hD : ∀ n m, n ≠ m → 0 ≤ D n m)
    (hW : ∀ n m, 0 ≤ W n m) {ρ σ : Fin N → ℝ}
    (hρ : ρ ∈ cube N) (hσ : σ ∈ cube N)
    (hminρ : ∀ τ ∈ cube N, Gen w L D W ρ ≤ Gen w L D W τ)
    (hminσ : ∀ τ ∈ cube N, Gen w L D W σ ≤ Gen w L D W τ) : ρ = σ := by
  by_contra hne
  have hmid : (fun n => (ρ n + σ n) / 2) ∈ cube N := by
    intro n
    have h1 := hρ n
    have h2 := hσ n
    exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  have hs := (Gen_midpoint w L D W hw hD hW hρ hσ).2 hne
  have h1 := hminρ _ hmid
  have h2 := hminσ _ hmid
  linarith

/-- Restricting a convex function to a line segment in the cube preserves convexity. -/
private theorem cube_segment_convexOn {N : ℕ} (f : (Fin N → ℝ) → ℝ)
    (hf : ConvexOn ℝ (cube N) f) {ρ σ : Fin N → ℝ}
    (hρ : ρ ∈ cube N) (hσ : σ ∈ cube N) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => f (ρ + t • (σ - ρ))) := by
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ρ + t • (σ - ρ) ∈ cube N := by
    have h := hf.1 hρ hσ (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    have heq : ρ + t • (σ - ρ) = (1 - t) • ρ + t • σ := by
      funext n
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact h
  constructor
  · exact convex_Icc _ _
  · intro x hx y hy a b ha hb hab
    have h := hf.2 (hline x hx) (hline y hy) ha hb hab
    have heq : ρ + (a * x + b * y) • (σ - ρ) =
        a • (ρ + x • (σ - ρ)) + b • (ρ + y • (σ - ρ)) := by
      funext n
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination -(ρ n) * hab
    change f (ρ + (a * x + b * y) • (σ - ρ)) ≤
      a * f (ρ + x • (σ - ρ)) + b * f (ρ + y • (σ - ρ))
    rw [heq]
    simpa only [smul_eq_mul] using h

/-- For a convex function, nonnegative one-sided derivatives along all feasible
segments characterize a global minimum. -/
theorem cube_stationary_is_min {N : ℕ} (f : (Fin N → ℝ) → ℝ)
    (hf : ConvexOn ℝ (cube N) f) {ρ : Fin N → ℝ} (hρ : ρ ∈ cube N)
    (hderiv : ∀ σ ∈ cube N, ∃ d : ℝ, 0 ≤ d ∧
      HasDerivWithinAt (fun t : ℝ => f (ρ + t • (σ - ρ))) d (Set.Ici 0) 0) :
    ∀ σ ∈ cube N, f ρ ≤ f σ := by
  intro σ hσ
  obtain ⟨d, hd, hdiff⟩ := hderiv σ hσ
  have hc := cube_segment_convexOn f hf hρ hσ
  have hs := hc.le_slope_of_hasDerivWithinAt_Ioi
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (by norm_num : (0 : ℝ) < 1)
    (hdiff.mono Set.Ioi_subset_Ici_self)
  simp only [slope_def_field, sub_zero, div_one, zero_smul, add_zero, one_smul] at hs
  have heq : ρ + (σ - ρ) = σ := by abel
  rw [heq] at hs
  linarith

theorem Gen_stationary_is_min {N : ℕ} (w L : Fin N → ℝ)
    (D W : Fin N → Fin N → ℝ) (hw : ∀ n, 0 < w n)
    (hD : ∀ n m, n ≠ m → 0 ≤ D n m) (hW : ∀ n m, 0 ≤ W n m)
    {ρ : Fin N → ℝ} (hρ : ρ ∈ cube N)
    (hderiv : ∀ σ ∈ cube N, ∃ d : ℝ, 0 ≤ d ∧
      HasDerivWithinAt (fun t : ℝ => Gen w L D W (ρ + t • (σ - ρ)))
        d (Set.Ici 0) 0) :
    ∀ σ ∈ cube N, Gen w L D W ρ ≤ Gen w L D W σ :=
  cube_stationary_is_min (Gen w L D W) (Gen_convexOn w L D W hw hD hW) hρ hderiv

/-- An interior or boundary point with zero Fréchet derivative is a minimum. -/
theorem Gen_fderiv_zero_is_min {N : ℕ} (w L : Fin N → ℝ)
    (D W : Fin N → Fin N → ℝ) (hw : ∀ n, 0 < w n)
    (hD : ∀ n m, n ≠ m → 0 ≤ D n m) (hW : ∀ n m, 0 ≤ W n m)
    {ρ : Fin N → ℝ} (hρ : ρ ∈ cube N)
    (hd : HasFDerivAt (Gen w L D W) (0 : (Fin N → ℝ) →L[ℝ] ℝ) ρ) :
    ∀ σ ∈ cube N, Gen w L D W ρ ≤ Gen w L D W σ := by
  apply Gen_stationary_is_min w L D W hw hD hW hρ
  intro σ hσ
  refine ⟨0, le_rfl, ?_⟩
  have hline : HasDerivAt (fun t : ℝ => ρ + t • (σ - ρ)) (σ - ρ) 0 := by
    change HasDerivAt ((fun _ : ℝ => ρ) + fun t : ℝ => t • (σ - ρ)) (σ - ρ) 0
    simpa only [zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) ρ).add
      ((hasDerivAt_id' (0 : ℝ)).smul_const (σ - ρ))
  have h := hd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  simpa only [Function.comp_def, ContinuousLinearMap.zero_apply] using h.hasDerivWithinAt

end KayThermo
