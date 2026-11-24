module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenPi
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

theorem _root_.GlobalTheory.T.quaternionNormOneTraceOpen_pi : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i), (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  first | exact @GlobalTheory.QSA.traceOpen_pi | exact GlobalTheory.QSA.traceOpen_pi | (intros; apply GlobalTheory.QSA.traceOpen_pi <;> assumption)
