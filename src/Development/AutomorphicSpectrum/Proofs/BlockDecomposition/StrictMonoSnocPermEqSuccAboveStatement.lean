module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fin.Tuple.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAbove
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

theorem _root_.GlobalTheory.T.strictMono_snoc_perm_eq_succAbove : ∀ {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 1))), StrictMono I →
    Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π → I = k.succAbove := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm | exact GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm <;> assumption)
