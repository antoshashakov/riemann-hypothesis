module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithful
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI := by
  first | exact @GlobalTheory.TiltFaithful.faithH | exact GlobalTheory.TiltFaithful.faithH | (intros; apply GlobalTheory.TiltFaithful.faithH <;> assumption)
