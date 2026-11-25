module

public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

noncomputable section

namespace HcS.UG

abbrev cT {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A :=
  (M.map σ).transpose

abbrev Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

abbrev Upq := @Formalism.UG.Upq

end HcS.UG

namespace HcS.BasicNotions

abbrev UpqT := @Formalism.BasicNotions.UpqT
abbrev UpqT.mat {P Q : ℕ} (g : UpqT P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  Formalism.BasicNotions.UpqT.mat g
abbrev lieU := @Formalism.BasicNotions.lieU
abbrev CDHaar := @Formalism.BasicNotions.CDHaar

end HcS.BasicNotions

end
