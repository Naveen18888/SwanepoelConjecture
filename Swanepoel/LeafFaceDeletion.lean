module
public import Swanepoel.L38HalfAreaFaces
public import Swanepoel.OuterFace
public import Mathlib.SetTheory.Cardinal.Finite
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

def PennyGraph.faceDeletionPoint {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) : Plane :=
  Classical.choose F.property.nonempty

theorem PennyGraph.faceDeletionPoint_mem {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    G.faceDeletionPoint F ∈ F.val := Classical.choose_spec F.property.nonempty

def PennyGraph.faceDeletionMap {n m : ℕ} (G : PennyGraph n) (H : PennyGraph m)
    (hHG : H.drawing ⊆ G.drawing) (F : PlaneFace G) : PlaneFace H :=
  ⟨connectedComponentIn H.drawingᶜ (G.faceDeletionPoint F),
    ⟨G.faceDeletionPoint F,fun hz =>
      G.face_subset_complement F (G.faceDeletionPoint_mem F) (hHG hz),rfl⟩⟩

theorem PennyGraph.faceDeletionMap_contains {n m : ℕ} (G : PennyGraph n) (H : PennyGraph m)
    (hHG : H.drawing ⊆ G.drawing) (F : PlaneFace G) :
    F.val ⊆ (G.faceDeletionMap H hHG F).val := by
  have hcompl : F.val ⊆ H.drawingᶜ := by
    intro z hz hdraw
    exact G.face_subset_complement F hz (hHG hdraw)
  exact (G.face_preconnected F).subset_connectedComponentIn (G.faceDeletionPoint_mem F) hcompl

theorem PennyGraph.faceDeletionMap_surjective {n m : ℕ} (G : PennyGraph n) (H : PennyGraph m)
    (hHG : H.drawing ⊆ G.drawing) : Function.Surjective (G.faceDeletionMap H hHG) := by
  intro K
  obtain ⟨x,hxG,hxK⟩ := G.dense_complement_drawing.exists_mem_open
    K.property.isOpen K.property.nonempty
  let F : PlaneFace G := ⟨connectedComponentIn G.drawingᶜ x,⟨x,hxG,rfl⟩⟩
  have hxF : x∈F.val := mem_connectedComponentIn hxG
  have hxMap := G.faceDeletionMap_contains H hHG F hxF
  refine ⟨F,Subtype.ext ?_⟩
  exact ((G.faceDeletionMap H hHG F).property.eq_component hxMap).trans
    (K.property.eq_component hxK).symm

theorem PennyGraph.faceDeletionMap_bijective_of_card {n m : ℕ} (G : PennyGraph n) (H : PennyGraph m)
    (hHG : H.drawing ⊆ G.drawing)
    (hcard : Nat.card (PlaneFace G)=Nat.card (PlaneFace H)) :
    Function.Bijective (G.faceDeletionMap H hHG) :=
  (Nat.bijective_iff_surjective_and_card _).mpr ⟨G.faceDeletionMap_surjective H hHG,hcard⟩

theorem PennyGraph.faceDeletionMap_bounded_iff_of_card {n m : ℕ} (G : PennyGraph n) (H : PennyGraph m)
    (hHG : H.drawing ⊆ G.drawing)
    (hcard : Nat.card (PlaneFace G)=Nat.card (PlaneFace H)) (F : PlaneFace G) :
    Bornology.IsBounded (G.faceDeletionMap H hHG F).val ↔ Bornology.IsBounded F.val := by
  constructor
  · intro hb
    exact hb.subset (G.faceDeletionMap_contains H hHG F)
  · intro hb
    by_contra hnew
    obtain ⟨O,hO,_huniqueG⟩ := G.exists_unique_outer_face
    have hMapO : ¬Bornology.IsBounded (G.faceDeletionMap H hHG O).val := by
      intro hbound
      exact hO (hbound.subset (G.faceDeletionMap_contains H hHG O))
    obtain ⟨_Q,_hQ,huniqueH⟩ := H.exists_unique_outer_face
    have heq : G.faceDeletionMap H hHG F=G.faceDeletionMap H hHG O :=
      (huniqueH _ hnew).trans (huniqueH _ hMapO).symm
    have hFO := (G.faceDeletionMap_bijective_of_card H hHG hcard).1 heq
    exact hO (hFO ▸ hb)

theorem PennyGraph.faceDeletionMap_sourceFace {n m : ℕ} (G : PennyGraph n) (H : PennyGraph m)
    (hHG : H.drawing ⊆ G.drawing) (e : OrientedEdge G) (f : OrientedEdge H)
    (hvector : carriedVector f=carriedVector e)
    (hmid : H.edgePoint f.val.1 f.val.2 (1/2)=G.edgePoint e.val.1 e.val.2 (1/2)) :
    G.faceDeletionMap H hHG (G.sourceFace e)=H.sourceFace f := by
  obtain ⟨z,hz⟩ := (G.sourceFace e).property.nonempty
  have hzMap := G.faceDeletionMap_contains H hHG (G.sourceFace e) hz
  have hzNew := G.sourceFace_subset_of_drawing_subset H hHG e f hvector hmid hz
  apply Subtype.ext
  exact ((G.faceDeletionMap H hHG (G.sourceFace e)).property.eq_component hzMap).trans
    ((H.sourceFace f).property.eq_component hzNew).symm

theorem PennyGraph.sourceFace_bounded_iff_of_drawing_subset_of_card {n m : ℕ}
    (G : PennyGraph n) (H : PennyGraph m) (hHG : H.drawing ⊆ G.drawing)
    (hcard : Nat.card (PlaneFace G)=Nat.card (PlaneFace H))
    (e : OrientedEdge G) (f : OrientedEdge H)
    (hvector : carriedVector f=carriedVector e)
    (hmid : H.edgePoint f.val.1 f.val.2 (1/2)=G.edgePoint e.val.1 e.val.2 (1/2)) :
    Bornology.IsBounded (G.sourceFace e).val ↔ Bornology.IsBounded (H.sourceFace f).val := by
  have h := G.faceDeletionMap_bounded_iff_of_card H hHG hcard (G.sourceFace e)
  rw [G.faceDeletionMap_sourceFace H hHG e f hvector hmid] at h
  exact h.symm

end Swanepoel
