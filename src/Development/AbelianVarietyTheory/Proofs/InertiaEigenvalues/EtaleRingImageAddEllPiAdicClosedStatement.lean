module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingImageAddEllPiAdicClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleRing_image_add_ell_pi_adic_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL), (∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) → ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  first | exact @GlobalTheory.Decompl.ioE_closed | exact GlobalTheory.Decompl.ioE_closed | (intros; apply GlobalTheory.Decompl.ioE_closed <;> assumption)
