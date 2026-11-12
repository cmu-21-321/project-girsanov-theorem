import Mathlib

/-!
# Basic definitions for the Girsanov theorem

This file gives the basic objects for the finite-time Girsanov theorem.

* `TimeGrid` is a list of observation times.
* `girsanovDensity` is the Girsanov density on a probability space.
* `girsanovMeasure` is the new measure `Q`. It has the Girsanov density with respect to `P`.
* `canonicalDensity` is the Girsanov density on the space `Fin n → ℝ`.
* `incrementLaw` is the law of the increments under `P`.
* The walk is Mathlib's `Fin.partialSum` of the increments; `measurable_partialSum` says
  that this map is measurable.
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

/-- Two consecutive times are in order: `t_k < t_{k+1}`. -/
lemma t_castSucc_lt_t_succ (k : Fin n) : g.t k.castSucc < g.t k.succ :=
  -- If Lean complains here, use `(Fin.castSucc_lt_succ k)` or `(by simp [Fin.lt_def])`.
  g.strictMono (Fin.castSucc_lt_succ ..)

/-- In `ℝ`, the increment `Δtₖ` is equal to `t_{k+1} - t_k`. -/
lemma coe_Δt (k : Fin n) : (g.Δt k : ℝ) = g.t k.succ - g.t k.castSucc :=
  -- `toNNReal` does nothing to a number that is `≥ 0`.
  Real.coe_toNNReal _ (sub_nonneg.2 (g.t_castSucc_lt_t_succ k).le)

/-- Each time increment is more than `0`. -/
lemma Δt_pos (k : Fin n) : 0 < g.Δt k := by
  -- Move the goal to `ℝ`, where `coe_Δt` describes `Δtₖ`.
  rw [← NNReal.coe_pos, coe_Δt, sub_pos]
  exact g.t_castSucc_lt_t_succ k

/-- Each time increment is not `0`. -/
lemma Δt_ne_zero (k : Fin n) : g.Δt k ≠ 0 :=
  (g.Δt_pos k).ne'

/-- A telescoping sum over `Fin`: `∑ₖ (f (k+1) - f k) = f m - f 0`. -/
lemma sum_succ_sub_castSucc {m : ℕ} (f : Fin (m + 1) → ℝ) :
    ∑ k : Fin m, (f k.succ - f k.castSucc) = f (Fin.last m) - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- Split off the last term of the sum.
    rw [Fin.sum_univ_castSucc]
    -- The induction hypothesis, used for `f` restricted to the first `m + 1` times.
    have h := ih (fun i ↦ f i.castSucc)
    -- `k.castSucc.succ` and `k.succ.castSucc` are the same element; write both the same way.
    simp only [Fin.succ_castSucc] at h ⊢
    rw [h]
    simp only [Fin.succ_last, Fin.castSucc_zero, Nat.succ_eq_add_one]
    ring

/-- The sum of all the time increments is equal to the final time `T`. -/
lemma sum_Δt : ∑ k, (g.Δt k : ℝ) = g.T := by
  simp_rw [coe_Δt]
  rw [sum_succ_sub_castSucc, g.zero, sub_zero, T]

/-- The final time `T` is not less than `0`. -/
lemma T_nonneg : 0 ≤ g.T := by
  -- `T` is a sum of numbers that are `≥ 0`.
  rw [← g.sum_Δt]
  positivity

end TimeGrid

/-! ### The Girsanov density on a probability space -/

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

-- Author: Preme.

/-- The Girsanov density `Z = exp(-∑ₖ θₖ ΔWₖ - ½ ∑ₖ θₖ² Δtₖ)`. It is a real number, as on
paper. Only `girsanovMeasure` changes it into `ℝ≥0∞`, because `Measure.withDensity` needs a
density in `ℝ≥0∞`. -/
noncomputable def girsanovDensity (g : TimeGrid n) (θ : Fin n → ℝ) (ΔW : Fin n → Ω → ℝ)
    (ω : Ω) : ℝ :=
  Real.exp (-(∑ k, θ k * ΔW k ω) - (1 / 2) * ∑ k, θ k ^ 2 * (g.Δt k : ℝ))

/-- The Girsanov measure `Q`. The measure `Q` has the Girsanov density with respect to `P`:
`Q(A) = E_P[Z · 1_A]`. -/
noncomputable def girsanovMeasure (P : Measure Ω) (g : TimeGrid n) (θ : Fin n → ℝ)
    (ΔW : Fin n → Ω → ℝ) : Measure Ω :=
  P.withDensity fun ω ↦ ENNReal.ofReal (girsanovDensity g θ ΔW ω)

-- Author: Hagen.
section API

variable (g : TimeGrid n) (θ : Fin n → ℝ) (ΔW : Fin n → Ω → ℝ)

/-- If each increment `ΔWₖ` is measurable, then the Girsanov density is measurable. -/
lemma measurable_girsanovDensity (hΔW : ∀ k, Measurable (ΔW k)) :
    Measurable (girsanovDensity g θ ΔW) := by
  unfold girsanovDensity
  fun_prop

omit [MeasurableSpace Ω] in
/-- The Girsanov density is positive. -/
lemma girsanovDensity_pos (ω : Ω) : 0 < girsanovDensity g θ ΔW ω :=
  Real.exp_pos _

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

/-- The Girsanov weight for one step: `x ↦ exp(-θ x - θ² v / 2)`.
This weight changes `𝒩(0, v)` into `𝒩(-θ v, v)`. -/
noncomputable def tiltWeight (θ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (-θ * x - θ ^ 2 * (v : ℝ) / 2)

/-- The Girsanov density on the canonical space `Fin n → ℝ`.
Coordinate `k` is the increment of step `k`.
The density is the product of the weights of all steps. -/
noncomputable abbrev canonicalDensity (g : TimeGrid n) (θ x : Fin n → ℝ) : ℝ :=
  ∏ k, tiltWeight (θ k) (g.Δt k) (x k)

/-- The law of the increments under `P`. This law is the product measure `⨂ₖ 𝒩(0, Δtₖ)`. -/
noncomputable abbrev incrementLaw (g : TimeGrid n) : Measure (Fin n → ℝ) :=
  Measure.pi fun k ↦ gaussianReal 0 (g.Δt k)

/-- The weight for one time step is measurable. -/
@[fun_prop]
lemma measurable_tiltWeight (θ : ℝ) (v : ℝ≥0) : Measurable (tiltWeight θ v) := by
    unfold tiltWeight
    fun_prop

/-- The weight for one time step is positive. -/
lemma tiltWeight_pos (θ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 < tiltWeight θ v x :=
  Real.exp_pos _

/-- The canonical density is measurable. -/
@[fun_prop]
lemma measurable_canonicalDensity (g : TimeGrid n) (θ : Fin n → ℝ) :
    Measurable (canonicalDensity g θ) := by
    unfold canonicalDensity
    fun_prop

/-- The canonical density is equal to `exp(-∑ₖ θₖ xₖ - ½ ∑ₖ θₖ² Δtₖ)`. -/
lemma canonicalDensity_eq_exp_sum (g : TimeGrid n) (θ x : Fin n → ℝ) :
    canonicalDensity g θ x =
      Real.exp (-(∑ k, θ k * x k) - (1 / 2) * ∑ k, θ k ^ 2 * (g.Δt k : ℝ)) := by
  unfold canonicalDensity tiltWeight
  -- Change the product of exponentials into the exponential of a sum.
  rw [← Real.exp_sum]
  -- Compare the two exponents.
  congr 1
  -- Change the right side into one sum `∑ k, (…)`.
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  -- Compare the two sums term by term.
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

omit [MeasurableSpace Ω] in
/-- The Girsanov density on `Ω` is equal to the canonical density of the increment vector.
-/
lemma girsanovDensity_eq_canonicalDensity_comp (g : TimeGrid n) (θ : Fin n → ℝ)
    (ΔW : Fin n → Ω → ℝ) :
    girsanovDensity g θ ΔW = canonicalDensity g θ ∘ (fun ω k ↦ ΔW k ω) := by
  funext ω
  -- Write the canonical density in closed form. Then the two sides are the same formula.
  rw [Function.comp_apply, canonicalDensity_eq_exp_sum]
  rfl

-- Author: Preme.
omit [MeasurableSpace Ω] in
/-- The Girsanov density is equal to a product. Each factor of the product has one time
step. -/
lemma girsanovDensity_eq_prod (g : TimeGrid n) (θ : Fin n → ℝ) (ΔW : Fin n → Ω → ℝ)
    (ω : Ω) :
    girsanovDensity g θ ΔW ω =
      ∏ k, Real.exp (-θ k * ΔW k ω - θ k ^ 2 * (g.Δt k : ℝ) / 2) :=
  congrFun (girsanovDensity_eq_canonicalDensity_comp g θ ΔW) ω

/-! ### The walk

We use Mathlib's `Fin.partialSum` for the walk. For increments `x : Fin n → ℝ`,
`Fin.partialSum x : Fin (n + 1) → ℝ` is the walk at the times `t₀, …, tₙ`:
`Fin.partialSum x 0 = 0` and `Fin.partialSum x i.succ = Fin.partialSum x i.castSucc + x i`. -/

-- Author: Hagen, Farin, Preme.
/-- The partial-sum map, which changes increments into the walk, is measurable. -/
@[fun_prop]
lemma measurable_partialSum :
    Measurable (Fin.partialSum : (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
  -- A map into a product is measurable if each coordinate is measurable.
  rw [measurable_pi_iff]
  intro i
  -- Induction on the time index: `W₀ = 0`, and `W_{i+1} = W_i + xᵢ`.
  induction i using Fin.induction with
  | zero =>
    simp only [Fin.partialSum_zero]
    exact measurable_const
  | succ j ih =>
    simp only [Fin.partialSum_succ]
    exact ih.add (measurable_pi_apply j)

end Girsanov
