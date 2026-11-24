module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfInertiaFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y → ∀ g : GQ l, Per.σC g y = y := by
  first | exact @GlobalTheory.RegularDense.fixed_of_inertia_frobenius | exact GlobalTheory.RegularDense.fixed_of_inertia_frobenius | (intros; apply GlobalTheory.RegularDense.fixed_of_inertia_frobenius <;> assumption)
