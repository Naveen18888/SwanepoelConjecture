module
public import Swanepoel.FaceDualConnectivity
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.face_values_constant_of_contact_agreement {n : ℕ} (G : PennyGraph n)
    {A : Type*} (value : PlaneFace G → A)
    (hagree : ∀ e : ContactEdge G,
      value (G.sourceFace e.forwardEdge) = value (G.sourceFace (reverseEdge e.forwardEdge)))
    (F H : PlaneFace G) : value F = value H := by
  have hinvariant (e : ContactEdge G) :
      (value (G.sourceFace e.forwardEdge) = value F) ↔
        value (G.sourceFace (reverseEdge e.forwardEdge)) = value F := by rw [hagree e]
  exact (G.face_predicate_constant_of_edge_invariant (fun K => value K = value F)
    hinvariant F rfl H).symm

def PennyGraph.boundedFaceAsPlane {n : ℕ} (G : PennyGraph n) (F : BoundedFace G) : PlaneFace G :=
  ⟨F.val,F.property.1⟩

theorem PennyGraph.boundedFaceAsPlane_injective {n : ℕ} (G : PennyGraph n) :
    Function.Injective G.boundedFaceAsPlane := by
  intro F H he
  exact Subtype.ext (congrArg (fun K : PlaneFace G => K.val) he)

def PennyGraph.faceIncidence {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) : ContactEdge G → ℝ :=
  fun e => (if G.sourceFace e.forwardEdge = F then 1 else 0) -
    (if G.sourceFace (reverseEdge e.forwardEdge) = F then 1 else 0)

def PennyGraph.boundedFaceIncidence {n : ℕ} (G : PennyGraph n) (F : BoundedFace G) : ContactEdge G → ℝ :=
  G.faceIncidence (G.boundedFaceAsPlane F)

def PennyGraph.extendBoundedFaceValues {n : ℕ} (G : PennyGraph n)
    (c : BoundedFace G → ℝ) (H : PlaneFace G) : ℝ :=
  if hb : Bornology.IsBounded H.val then c ⟨H.val,H.property,hb⟩ else 0

theorem PennyGraph.extendBoundedFaceValues_bounded {n : ℕ} (G : PennyGraph n)
    (c : BoundedFace G → ℝ) (F : BoundedFace G) :
    G.extendBoundedFaceValues c (G.boundedFaceAsPlane F) = c F := by
  simp [PennyGraph.extendBoundedFaceValues,PennyGraph.boundedFaceAsPlane,F.property.2]

theorem PennyGraph.extendBoundedFaceValues_unbounded {n : ℕ} (G : PennyGraph n)
    (c : BoundedFace G → ℝ) (H : PlaneFace G) (hH : ¬ Bornology.IsBounded H.val) :
    G.extendBoundedFaceValues c H = 0 := by
  simp only [PennyGraph.extendBoundedFaceValues,dite_eq_right hH]

theorem PennyGraph.sum_bounded_face_indicator {n : ℕ} (G : PennyGraph n)
    (c : BoundedFace G → ℝ) (H : PlaneFace G) :
    (∑ F : BoundedFace G, c F*(if H = G.boundedFaceAsPlane F then 1 else 0)) =
      G.extendBoundedFaceValues c H := by
  by_cases hb : Bornology.IsBounded H.val
  · let B : BoundedFace G := ⟨H.val,H.property,hb⟩
    have hBH : G.boundedFaceAsPlane B = H := Subtype.ext rfl
    have hsel (F : BoundedFace G) : H = G.boundedFaceAsPlane F ↔ F = B := by
      constructor
      · intro he
        exact Subtype.ext (congrArg (fun K : PlaneFace G => K.val) he).symm
      · intro he
        rw [he]
        exact hBH.symm
    simp only [PennyGraph.extendBoundedFaceValues,dite_eq_left hb]
    change (∑ F : BoundedFace G, c F*(if H = G.boundedFaceAsPlane F then 1 else 0)) = c B
    simp only [hsel,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · have hne (F : BoundedFace G) : H ≠ G.boundedFaceAsPlane F := by
      intro he
      apply hb
      have hval := congrArg (fun K : PlaneFace G => K.val) he
      rw [hval]
      exact F.property.2
    simp only [hne,ite_false,mul_zero,Finset.sum_const_zero,
      PennyGraph.extendBoundedFaceValues,dite_eq_right hb]

theorem PennyGraph.boundedFaceIncidence_combination_apply {n : ℕ} (G : PennyGraph n)
    (c : BoundedFace G → ℝ) (e : ContactEdge G) :
    (∑ F : BoundedFace G, c F • G.boundedFaceIncidence F) e =
      G.extendBoundedFaceValues c (G.sourceFace e.forwardEdge) -
        G.extendBoundedFaceValues c (G.sourceFace (reverseEdge e.forwardEdge)) := by
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,PennyGraph.boundedFaceIncidence,
    PennyGraph.faceIncidence,mul_sub,Finset.sum_sub_distrib,G.sum_bounded_face_indicator]

theorem PennyGraph.boundedFaceIncidence_coefficients_zero {n : ℕ} (G : PennyGraph n)
    (c : BoundedFace G → ℝ) (hsum : (∑ F : BoundedFace G, c F • G.boundedFaceIncidence F) = 0) :
    ∀ F : BoundedFace G, c F = 0 := by
  have hagree (e : ContactEdge G) :
      G.extendBoundedFaceValues c (G.sourceFace e.forwardEdge) =
        G.extendBoundedFaceValues c (G.sourceFace (reverseEdge e.forwardEdge)) := by
    have he : (∑ F : BoundedFace G, c F • G.boundedFaceIncidence F) e = 0 := congrFun hsum e
    rw [G.boundedFaceIncidence_combination_apply] at he
    exact sub_eq_zero.mp he
  obtain ⟨outer,houter,_⟩ := G.exists_unique_outer_face
  intro F
  calc
    _ = G.extendBoundedFaceValues c (G.boundedFaceAsPlane F) :=
      (G.extendBoundedFaceValues_bounded c F).symm
    _ = G.extendBoundedFaceValues c outer := G.face_values_constant_of_contact_agreement _ hagree _ _
    _ = 0 := G.extendBoundedFaceValues_unbounded c outer houter

theorem PennyGraph.boundedFaceIncidence_linearIndependent {n : ℕ} (G : PennyGraph n) :
    LinearIndependent ℝ G.boundedFaceIncidence := by
  apply Fintype.linearIndependent_iff.mpr
  exact fun c hc => G.boundedFaceIncidence_coefficients_zero c hc

end Swanepoel
