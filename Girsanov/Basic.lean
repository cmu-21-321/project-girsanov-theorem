import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Girsanov

/-! ### Time grid -/

-- Preme's part

/-- A strictly increasing time grid `0 = t₀ < t₁ < … < tₙ`. -/
structure TimeGrid (n : ℕ) where
  /-- The observation times. -/
  t : Fin (n + 1) → ℝ
  strictMono : StrictMono t
  zero : t 0 = 0

namespace TimeGrid

variable {n : ℕ} (g : TimeGrid n)

/-- The final time `T = tₙ`. -/
def T : ℝ := g.t (Fin.last n)

/-- The `k`-th time increment `Δtₖ = t_{k+1} - t_k`, as an `ℝ≥0` variance. -/
noncomputable def Δt (k : Fin n) : ℝ≥0 :=
  (g.t k.succ - g.t k.castSucc).toNNReal

lemma coe_Δt (k : Fin n) : (g.Δt k : ℝ) = g.t k.succ - g.t k.castSucc := by
  sorry

lemma Δt_pos (k : Fin n) : 0 < g.Δt k := by
  sorry

lemma Δt_ne_zero (k : Fin n) : g.Δt k ≠ 0 := by
  sorry

/-- The increments telescope to the final time. -/
lemma sum_Δt : ∑ k, (g.Δt k : ℝ) = g.T := by
  sorry

lemma T_nonneg : 0 ≤ g.T := by
  sorry

end TimeGrid

/-! ### The Girsanov density on an abstract probability space -/

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

-- Preme's part

/-- The Girsanov density `exp(-∑ₖ θₖ ΔWₖ - ½ ∑ₖ θₖ² Δtₖ)`. -/
noncomputable def girsanovDensity (g : TimeGrid n) (θ : Fin n → ℝ) (ΔW : Fin n → Ω → ℝ)
    (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-(∑ k, θ k * ΔW k ω) - (1 / 2) * ∑ k, θ k ^ 2 * (g.Δt k : ℝ)))

/-- The Girsanov measure `Q = P.withDensity girsanovDensity`. -/
noncomputable def girsanovMeasure (P : Measure Ω) (g : TimeGrid n) (θ : Fin n → ℝ)
    (ΔW : Fin n → Ω → ℝ) : Measure Ω :=
  P.withDensity (girsanovDensity g θ ΔW)

-- Hagen's part
section API

variable (g : TimeGrid n) (θ : Fin n → ℝ) (ΔW : Fin n → Ω → ℝ)

lemma measurable_girsanovDensity (hΔW : ∀ k, Measurable (ΔW k)) :
    Measurable (girsanovDensity g θ ΔW) := by
  unfold girsanovDensity
  fun_prop

omit [MeasurableSpace Ω] in
lemma girsanovDensity_ne_zero (ω : Ω) : girsanovDensity g θ ΔW ω ≠ 0 := by
  simp [girsanovDensity, Real.exp_pos]

omit [MeasurableSpace Ω] in
lemma girsanovDensity_ne_top (ω : Ω) : girsanovDensity g θ ΔW ω ≠ ∞ := by
  simp [girsanovDensity]

-- Preme's part
lemma girsanovDensity_eq_prod (ω : Ω) :
    girsanovDensity g θ ΔW ω =
      ∏ k, ENNReal.ofReal (Real.exp (-θ k * ΔW k ω - θ k ^ 2 * (g.Δt k : ℝ) / 2)) := by
  sorry

-- Hagen's part
omit [MeasurableSpace Ω] in
/-- With zero drift the density is `1`. -/
@[simp]
lemma girsanovDensity_zero : girsanovDensity g 0 ΔW = 1 := by
  ext ω
  simp [girsanovDensity]

/-- With zero drift, `Q = P`. -/
@[simp]
lemma girsanovMeasure_zero (P : Measure Ω) : girsanovMeasure P g 0 ΔW = P := by
  simp [girsanovMeasure]

end API

/-! ### The canonical space `Fin n → ℝ` -/

-- Farin's part

/-- The one-step Girsanov weight `x ↦ exp(-θ x - θ² v / 2)`. Reweighting `𝒩(0, v)` by it
gives `𝒩(-θ v, v)`. -/
noncomputable def tiltWeight (θ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-θ * x - θ ^ 2 * (v : ℝ) / 2))

/-- The Girsanov density on the canonical space `Fin n → ℝ`, where coordinate `k` is the
`k`-th increment: the product of the one-step weights. -/
noncomputable def canonicalDensity (g : TimeGrid n) (θ x : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ k, tiltWeight (θ k) (g.Δt k) (x k)

/-- The law of the increments under `P`: `⨂ₖ 𝒩(0, Δtₖ)`. -/
noncomputable abbrev incrementLaw (g : TimeGrid n) : Measure (Fin n → ℝ) :=
  Measure.pi fun k ↦ gaussianReal 0 (g.Δt k)

@[fun_prop]
lemma measurable_tiltWeight (θ : ℝ) (v : ℝ≥0) : Measurable (tiltWeight θ v) := by
    unfold tiltWeight
    fun_prop

lemma tiltWeight_ne_zero (θ : ℝ) (v : ℝ≥0) (x : ℝ) : tiltWeight θ v x ≠ 0 := by
    simp [tiltWeight, Real.exp_pos]

lemma tiltWeight_ne_top (θ : ℝ) (v : ℝ≥0) (x : ℝ) : tiltWeight θ v x ≠ ∞ := by
    simp [tiltWeight]

@[fun_prop]
lemma measurable_canonicalDensity (g : TimeGrid n) (θ : Fin n → ℝ) :
    Measurable (canonicalDensity g θ) := by
    unfold canonicalDensity
    fun_prop

/-- The density in closed form: `exp(-∑ₖ θₖ xₖ - ½ ∑ₖ θₖ² Δtₖ)`. -/
lemma canonicalDensity_eq_exp_sum (g : TimeGrid n) (θ x : Fin n → ℝ) :
    canonicalDensity g θ x = ENNReal.ofReal
      (Real.exp (-(∑ k, θ k * x k) - (1 / 2) * ∑ k, θ k ^ 2 * (g.Δt k : ℝ))) := by
  sorry

omit [MeasurableSpace Ω] in
/-- The abstract density is the canonical one composed with the increment vector. -/
lemma girsanovDensity_eq_canonicalDensity_comp (g : TimeGrid n) (θ : Fin n → ℝ)
    (ΔW : Fin n → Ω → ℝ) :
    girsanovDensity g θ ΔW = canonicalDensity g θ ∘ (fun ω k ↦ ΔW k ω) := by
  sorry

-- Hagen's part
/-- The partial-sum map sending increments to the walk `Wₖ = ∑_{j ≤ k} ΔWⱼ`. -/
def partialSums (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ j : Fin n with j ≤ k, x j

-- Farin's part
lemma measurable_partialSums : Measurable (partialSums (n := n)) := by
  unfold partialSums
  fun_prop

end Girsanov
