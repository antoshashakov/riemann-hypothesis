module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesEqCOfSubstFixedNotRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

theorem _root_.GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity : ∀ (L : Type) [Field L] (y : PowerSeries L), PowerSeries.constantCoeff y = 0 → (∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) → ∀ a : PowerSeries L, (PowerSeries.subst y a : PowerSeries L) = a → a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  first | exact @GlobalTheory.powerSeries_eq_C_of_subst_eq_self | exact GlobalTheory.powerSeries_eq_C_of_subst_eq_self | (intros; apply GlobalTheory.powerSeries_eq_C_of_subst_eq_self <;> assumption)
