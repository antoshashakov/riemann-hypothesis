module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotientStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ImageLatticeBaseChange

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.lattice_image_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) :=
  @_root_.PositivityTheory.Xgn.image_lattice_base_change
