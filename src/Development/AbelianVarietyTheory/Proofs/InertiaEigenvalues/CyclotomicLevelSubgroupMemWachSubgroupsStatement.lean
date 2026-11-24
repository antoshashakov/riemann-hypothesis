module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.cyclotomicLevelSubgroup_mem_wachSubgroups : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  first | exact @GlobalTheory.Cyc.Decomp.grp_GKs_H | exact GlobalTheory.Cyc.Decomp.grp_GKs_H | (intros; apply GlobalTheory.Cyc.Decomp.grp_GKs_H <;> assumption)
