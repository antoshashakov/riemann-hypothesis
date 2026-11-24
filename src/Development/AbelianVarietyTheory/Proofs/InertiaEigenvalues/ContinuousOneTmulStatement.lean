module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOneTmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



theorem _root_.GlobalTheory.T.continuous_one_tmul_latB : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d), letI := twTop T b; Continuous fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t := by
  first | exact @GlobalTheory.WeakClosed.continuous_one_tmul | exact GlobalTheory.WeakClosed.continuous_one_tmul | (intros; apply GlobalTheory.WeakClosed.continuous_one_tmul <;> assumption)
