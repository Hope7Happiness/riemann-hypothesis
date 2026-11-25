module

public import Formalism.LocalRingCardinality.DataCD
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Algebra.Group.Units
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BaseLatticeIsUnimodular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

@[expose] public section

noncomputable section

namespace HcInf

open NumberField IsDedekindDomain Formalism.BasicNotions Matrix MeasureTheory Filter Topology
open scoped TensorProduct ENNReal NNReal

section Upq

variable (P Q : ℕ)

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem cT_eq (X : Mat) : Formalism.UG.cT (starRingEnd ℂ) X = Xᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem Jpq_mul_self : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem Jpq_conjTranspose : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem mem_Upq_iff (g : GL (Fin P ⊕ Fin Q) ℂ) :
    g ∈ Formalism.UG.Upq P Q ↔ (g : Mat)ᴴ * Formalism.UG.Jpq P Q * (g : Mat) = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Upq
  rw [← cT_eq]
  rfl

def toS (g : UpqT P Q) : Formalism.UG.Upq P Q := g

theorem mat_eq (g : UpqT P Q) : UpqT.mat g = ((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ) : Mat) := rfl

theorem mat_inv (g : UpqT P Q) :
    (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) =
      Formalism.UG.Jpq P Q * (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q := by
  have hmem : (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := by
    rw [mat_eq]
    exact (mem_Upq_iff P Q _).mp (toS P Q g).2
  have hAB : UpqT.mat g * (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) = 1 := by
    rw [mat_eq, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat)
      = (Formalism.UG.Jpq P Q * ((UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g)) *
          (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat) := by
        rw [hmem, Jpq_mul_self, Matrix.one_mul]
    _ = Formalism.UG.Jpq P Q * (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q *
          (UpqT.mat g * (((toS P Q g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Mat)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hAB, Matrix.mul_one]

theorem isInducing_mat : IsInducing (UpqT.mat (P := P) (Q := Q)) := by
  apply _root_.GlobalTheory.UpqTopology.isInducing_mat <;> assumption

theorem range_mat : Set.range (UpqT.mat (P := P) (Q := Q)) =
    {X : Mat | Xᴴ * Formalism.UG.Jpq P Q * X = Formalism.UG.Jpq P Q} := by
  ext X
  constructor
  · rintro ⟨g, rfl⟩
    show (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q
    rw [mat_eq]
    exact (mem_Upq_iff P Q _).mp (toS P Q g).2
  · intro hX
    have hX' : Xᴴ * Formalism.UG.Jpq P Q * X = Formalism.UG.Jpq P Q := hX
    have hl : (Formalism.UG.Jpq P Q * Xᴴ * Formalism.UG.Jpq P Q) * X = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hX', Jpq_mul_self]
    have hr : X * (Formalism.UG.Jpq P Q * Xᴴ * Formalism.UG.Jpq P Q) = 1 := mul_eq_one_comm.mp hl
    let u : GL (Fin P ⊕ Fin Q) ℂ := ⟨X, _, hr, hl⟩
    have hu : u ∈ Formalism.UG.Upq P Q := (mem_Upq_iff P Q u).mpr hX'
    exact ⟨(⟨u, hu⟩ : Formalism.UG.Upq P Q), rfl⟩

theorem isClosedEmbedding_mat : IsClosedEmbedding (UpqT.mat (P := P) (Q := Q)) := by
  refine ⟨⟨isInducing_mat P Q, fun a b h => ?_⟩, ?_⟩
  · exact Subtype.ext (Units.ext h)
  · rw [range_mat]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const

instance : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))

instance : BorelSpace (UpqT P Q) := ⟨rfl⟩

instance : LocallyCompactSpace (UpqT P Q) := by
  haveI : LocallyCompactSpace Mat :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact (isClosedEmbedding_mat P Q).locallyCompactSpace

instance : SecondCountableTopology (UpqT P Q) := by
  haveI : SecondCountableTopology Mat :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact (isInducing_mat P Q).secondCountableTopology

end Upq

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : HcS.BasicNotions.CMData F E) (T : Type) [Fintype T] (cd : CDHaar)

end HcInf
