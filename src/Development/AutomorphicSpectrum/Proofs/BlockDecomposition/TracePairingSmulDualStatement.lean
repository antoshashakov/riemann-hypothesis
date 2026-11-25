module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
public import Mathlib.GroupTheory.GroupAction.Ring
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulDual
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_smul_dual : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPsi.T_ksmul | exact GlobalTheory.CompanionTheory.FrobPsi.T_ksmul | (intros; apply GlobalTheory.CompanionTheory.FrobPsi.T_ksmul <;> assumption)
