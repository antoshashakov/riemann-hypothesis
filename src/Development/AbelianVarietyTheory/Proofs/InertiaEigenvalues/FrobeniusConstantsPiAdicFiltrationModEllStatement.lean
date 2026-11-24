module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.frobenius_constants_piAdic_filtration_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧ NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧ (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧ ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) → ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  first | exact @GlobalTheory.DecomplFrob.frobenius_and_constants | exact GlobalTheory.DecomplFrob.frobenius_and_constants | (intros; apply GlobalTheory.DecomplFrob.frobenius_and_constants <;> assumption)
