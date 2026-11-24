module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescentGeometricPoints
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.etale_faithfullyFlat_descent_geometric_points : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  first | exact @GlobalTheory.EtaleGeomDescent.descent | exact GlobalTheory.EtaleGeomDescent.descent | (intros; apply GlobalTheory.EtaleGeomDescent.descent <;> assumption)
