import Mathlib

/-!
# Basic definitions for the Girsanov theorem

This file gives the basic objects for the finite-time Girsanov theorem.

* `TimeGrid` is a list of observation times.
* `girsanovDensity` is the Girsanov density on a probability space.
* `girsanovMeasure` is the new measure `Q`. It has the Girsanov density with respect to `P`.
* `canonicalDensity` is the Girsanov density on the space `Fin n → ℝ`.
* `incrementLaw` is the law of the increments under `P`.
* `partialSums` changes a vector of increments into a walk.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Girsanov

/-! ### Time grid -/

-- Author: Preme.

/-- A time grid `0 = t₀ < t₁ < … < tₙ`. Each time is larger than the time before it. -/
structure TimeGrid (n : ℕ) where
  /-- The observation times. -/
  t : Fin (n + 1) → ℝ
  /-- Each time is larger than the time before it. -/
  strictMono : StrictMono t
  /-- The first time is `0`. -/
  zero : t 0 = 0

namespace TimeGrid

variable {n : ℕ} (g : TimeGrid n)

/-- The final time `T = tₙ`. -/
def T : ℝ := g.t (Fin.last n)

/-- The time increment `Δtₖ = t_{k+1} - t_k`. Its type is `ℝ≥0` because we use it as a
variance. -/
noncomputable def Δt (k : Fin n) : ℝ≥0 :=
  (g.t k.succ - g.t k.castSucc).toNNReal

/-- In `ℝ`, the increment `Δtₖ` is equal to `t_{k+1} - t_k`. -/
lemma coe_Δt (k : Fin n) : (g.Δt k : ℝ) = g.t k.succ - g.t k.castSucc := by
  sorry

/-- Each time increment is more than `0`. -/
lemma Δt_pos (k : Fin n) : 0 < g.Δt k := by
  sorry

/-- Each time increment is not `0`. -/
lemma Δt_ne_zero (k : Fin n) : g.Δt k ≠ 0 := by
  sorry

/-- The sum of all the time increments is equal to the final time `T`. -/
lemma sum_Δt : ∑ k, (g.Δt k : ℝ) = g.T := by
  sorry

/-- The final time `T` is not less than `0`. -/
lemma T_nonneg : 0 ≤ g.T := by
  sorry

end TimeGrid

/-! ### The Girsanov density on a probability space -/

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

-- Author: Preme.

/-- The Girsanov density `exp(-∑ₖ θₖ ΔWₖ - ½ ∑ₖ θₖ² Δtₖ)`. -/
noncomputable def girsanovDensity (g : TimeGrid n) (θ : Fin n → ℝ) (ΔW : Fin n → Ω → ℝ)
    (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-(∑ k, θ k * ΔW k ω) - (1 / 2) * ∑ k, θ k ^ 2 * (g.Δt k : ℝ)))

/-- The Girsanov measure `Q`. The measure `Q` has the Girsanov density with respect to `P`. -/
noncomputable def girsanovMeasure (P : Measure Ω) (g : TimeGrid n) (θ : Fin n → ℝ)
    (ΔW : Fin n → Ω → ℝ) : Measure Ω :=
  P.withDensity (girsanovDensity g θ ΔW)

-- Author: Hagen.
section API

variable (g : TimeGrid n) (θ : Fin n → ℝ) (ΔW : Fin n → Ω → ℝ)

/-- If each increment `ΔWₖ` is measurable, then the Girsanov density is measurable. -/
lemma measurable_girsanovDensity (hΔW : ∀ k, Measurable (ΔW k)) :
    Measurable (girsanovDensity g θ ΔW) := by
  unfold girsanovDensity
  fun_prop

omit [MeasurableSpace Ω] in
/-- The Girsanov density is not `0` at a point. -/
lemma girsanovDensity_ne_zero (ω : Ω) : girsanovDensity g θ ΔW ω ≠ 0 := by
  simp [girsanovDensity, Real.exp_pos]

omit [MeasurableSpace Ω] in
/-- The Girsanov density is not `∞` at a point. -/
lemma girsanovDensity_ne_top (ω : Ω) : girsanovDensity g θ ΔW ω ≠ ∞ := by
  simp [girsanovDensity]

-- Author: Preme.
/-- The Girsanov density is equal to a product. Each factor of the product has one time
step. -/
lemma girsanovDensity_eq_prod (ω : Ω) :
    girsanovDensity g θ ΔW ω =
      ∏ k, ENNReal.ofReal (Real.exp (-θ k * ΔW k ω - θ k ^ 2 * (g.Δt k : ℝ) / 2)) := by
  sorry

-- Author: Hagen.
omit [MeasurableSpace Ω] in
/-- If the drift is `0`, then the density is `1`. -/
@[simp]
lemma girsanovDensity_zero : girsanovDensity g 0 ΔW = 1 := by
  ext ω
  simp [girsanovDensity]

/-- If the drift is `0`, then `Q` is equal to `P`. -/
@[simp]
lemma girsanovMeasure_zero (P : Measure Ω) : girsanovMeasure P g 0 ΔW = P := by
  simp [girsanovMeasure]

end API

/-! ### The canonical space `Fin n → ℝ` -/

-- Author: Farin.

<<<<<<< Updated upstream
/-- The Girsanov weight for one step: `x ↦ exp(-θ x - θ² v / 2)`.
This weight changes `𝒩(0, v)` into `𝒩(-θ v, v)`. -/
noncomputable def tiltWeight (θ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-θ * x - θ ^ 2 * (v : ℝ) / 2))

/-- The Girsanov density on the canonical space `Fin n → ℝ`.
Coordinate `k` is the increment of step `k`.
The density is the product of the weights of all steps. -/
=======
/-- The Girsanov weight for one time step: `x ↦ exp(-θ x - θ² v / 2)`. If you multiply
`𝒩(0, v)` by this weight, you get `𝒩(-θ v, v)`. -/
noncomputable def tiltWeight (θ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-θ * x - θ ^ 2 * (v : ℝ) / 2))

/-- The Girsanov density on the canonical space `Fin n → ℝ`. Coordinate `k` is the
increment `k`. The density is the product of the weights for each time step. -/
>>>>>>> Stashed changes
noncomputable def canonicalDensity (g : TimeGrid n) (θ x : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ k, tiltWeight (θ k) (g.Δt k) (x k)

/-- The law of the increments under `P`. This law is the product measure `⨂ₖ 𝒩(0, Δtₖ)`. -/
noncomputable abbrev incrementLaw (g : TimeGrid n) : Measure (Fin n → ℝ) :=
  Measure.pi fun k ↦ gaussianReal 0 (g.Δt k)

/-- The weight for one time step is measurable. -/
@[fun_prop]
lemma measurable_tiltWeight (θ : ℝ) (v : ℝ≥0) : Measurable (tiltWeight θ v) := by
    unfold tiltWeight
    fun_prop

/-- The weight for one time step is not `0`. -/
lemma tiltWeight_ne_zero (θ : ℝ) (v : ℝ≥0) (x : ℝ) : tiltWeight θ v x ≠ 0 := by
    simp [tiltWeight, Real.exp_pos]

/-- The weight for one time step is not `∞`. -/
lemma tiltWeight_ne_top (θ : ℝ) (v : ℝ≥0) (x : ℝ) : tiltWeight θ v x ≠ ∞ := by
    simp [tiltWeight]

/-- The canonical density is measurable. -/
@[fun_prop]
lemma measurable_canonicalDensity (g : TimeGrid n) (θ : Fin n → ℝ) :
    Measurable (canonicalDensity g θ) := by
    unfold canonicalDensity
    fun_prop

/-- The canonical density is equal to `exp(-∑ₖ θₖ xₖ - ½ ∑ₖ θₖ² Δtₖ)`. -/
lemma canonicalDensity_eq_exp_sum (g : TimeGrid n) (θ x : Fin n → ℝ) :
    canonicalDensity g θ x = ENNReal.ofReal
      (Real.exp (-(∑ k, θ k * x k) - (1 / 2) * ∑ k, θ k ^ 2 * (g.Δt k : ℝ))) := by
  unfold canonicalDensity tiltWeight
  -- Move `ofReal` outside the product. This is correct because each factor `exp _` is `≥ 0`.
  rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ ↦ by positivity)]
  -- Change the product of exponentials into the exponential of a sum.
  rw [← Real.exp_sum]
  -- Compare the two exponents.
  congr 2
  -- Change the right side into one sum `∑ k, (…)`.
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  -- Compare the two sums term by term.
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

omit [MeasurableSpace Ω] in
<<<<<<< Updated upstream
/-- The abstract density is the canonical density composed with the increment vector. -/
=======
/-- The Girsanov density on `Ω` is equal to the canonical density of the increment vector.
-/
>>>>>>> Stashed changes
lemma girsanovDensity_eq_canonicalDensity_comp (g : TimeGrid n) (θ : Fin n → ℝ)
    (ΔW : Fin n → Ω → ℝ) :
    girsanovDensity g θ ΔW = canonicalDensity g θ ∘ (fun ω k ↦ ΔW k ω) := by
  funext ω
  -- Write the canonical density in closed form. Then the two sides are the same formula.
  rw [Function.comp_apply, canonicalDensity_eq_exp_sum]
  rfl

-- Author: Hagen.
/-- The partial sums of the increments. This map changes the increments into the walk
`Wₖ = ∑_{j ≤ k} ΔWⱼ`. -/
def partialSums (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ j : Fin n with j ≤ k, x j

-- Author: Farin.
/-- The partial-sum map is measurable. -/
lemma measurable_partialSums : Measurable (partialSums (n := n)) := by
  unfold partialSums
  fun_prop

end Girsanov
