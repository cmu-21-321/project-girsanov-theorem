import Girsanov.Basic

/-!
# Product densities on product measures

If each factor `μ i` is reweighted by a density `f i`, then reweighting the
product measure by `x ↦ ∏ i, f i (x i)` gives the product of the reweighted factors.
This is the step that lets the Girsanov density on `Fin n → ℝ` be handled one coordinate
at a time.

## Plan for `pi_withDensity`

1. Two σ-finite product measures agree once they agree on every box `Set.univ.pi s` with
   measurable sides (`Measure.pi_eq`).
2. On a box, the left side is `∫⁻ x in Set.univ.pi s, ∏ i, f i (x i) ∂(Measure.pi μ)`
   (`withDensity_apply`, `MeasurableSet.univ_pi`).
3. The product measure restricted to a box is the product of the restrictions
   (`Measure.restrict_pi_pi`), and the integral of a product of one-variable functions
   against a product measure is the product of the integrals.
4. Each factor `∫⁻ y in s i, f i y ∂(μ i)` is `(μ i).withDensity (f i) (s i)`
   (`withDensity_apply` again).

## Step · Fact · Mathlib name

* Step 1. `Measure.pi μ = μ'` from agreement on boxes: `Measure.pi_eq`.
* Step 2. `μ.withDensity f s = ∫⁻ a in s, f a ∂μ` for measurable `s`: `withDensity_apply`.
* Step 2. A box with measurable sides is measurable: `MeasurableSet.univ_pi`.
* Setup. `μ.withDensity f` is σ-finite when `μ` is and `f` never takes the value `∞`:
  `SigmaFinite.withDensity_of_ne_top'`.
* Step 3b. Law of one coordinate under `Measure.pi`: `Measure.pi_map_eval`.
* Step 3. `(Measure.pi μ).restrict (univ.pi s) = Measure.pi fun i ↦ (μ i).restrict (s i)`:
  `Measure.restrict_pi_pi`.
* Step 3. `∫⁻` of `∏ i, f i (x i)` against `Measure.pi` is `∏ i, ∫⁻ f i`: **not found**
  (see note).

Note on step 3: Mathlib has the Bochner version `MeasureTheory.integral_fintype_prod_eq_prod`
but no `ℝ≥0∞` (`∫⁻`) version under an obvious name. Two routes:
* For probability measures (assumed in the statement: every factor is a Gaussian),
  the coordinates are independent under `Measure.pi` (`ProbabilityTheory.iIndepFun_pi`), so
  `ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun` splits the integral.
  Write the restricted integrand as `∏ i, (s i).indicator (f i) (x i)` first.
* For general σ-finite `μ`, induct on `n` with `MeasureTheory.measurePreserving_piFinSuccAbove`
  and `MeasureTheory.lintegral_prod_mul`. More work; only worth it if we upstream the lemma.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

#check @Measure.pi_eq
#check @withDensity_apply
#check @MeasurableSet.univ_pi
#check @Measure.restrict_pi_pi
#check @integral_fintype_prod_eq_prod
#check @lintegral_prod_eq_prod_lintegral_of_indepFun
#check @iIndepFun_pi
#check @SigmaFinite.withDensity_of_ne_top'
#check @Measure.pi_map_eval

namespace Girsanov

/-- A product density on a product of probability measures splits into factor densities.
Finiteness of each `f i` makes each reweighted factor σ-finite. -/
theorem pi_withDensity {ι : Type*} [Fintype ι]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {f : ι → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (hf_top : ∀ i x, f i x ≠ ∞) :
    (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i))
      = Measure.pi fun i ↦ (μ i).withDensity (f i) := by
  have : ∀ i, SigmaFinite ((μ i).withDensity (f i)) :=
    fun i ↦ SigmaFinite.withDensity_of_ne_top' (hf_top i)
  -- Step 1: `symm; refine Measure.pi_eq fun s hs ↦ ?_`
  -- Step 2: `rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]`
  -- Step 3: `rw [Measure.restrict_pi_pi]`, then split the product integral
  --   (`iIndepFun_pi`, `lintegral_prod_eq_prod_lintegral_of_indepFun`, `Measure.pi_map_eval`)
  -- Step 4: `simp_rw [withDensity_apply _ (hs _)]`
  sorry

end Girsanov
