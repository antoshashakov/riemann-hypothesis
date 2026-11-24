module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootPowIdealsTendstoZeroWeakTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



theorem _root_.GlobalTheory.T.teichmullerRootPow_ideals_tendsto_zero_weakTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ), letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ k : ℕ, ∀ z : Ainf l, inclW l ((WittVector.teichmuller l (AI.εroot s) - 1) ^ k * z) ∈ U := by
  first | exact @GlobalTheory.WeakClosed.SmallW.main | exact GlobalTheory.WeakClosed.SmallW.main | (intros; apply GlobalTheory.WeakClosed.SmallW.main <;> assumption)
