module
public import Swanepoel.FiniteFaces
@[expose] public section

noncomputable section
namespace Swanepoel

theorem RhombusCell.cellPoint_half_eq_center {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    C.cellPoint (1/2) (1/2)=C.center := by
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  dsimp [RhombusCell.cellPoint,RhombusCell.center,RhombusCell.midpoint2,RhombusCell.u,RhombusCell.v]
  rw [hc]
  module

theorem RhombusCell.openRegion_eq_of_corners {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (C D : RhombusCell G) (hc : C.corners=D.corners) :
    C.openRegion=D.openRegion := by
  rw [C.openRegion_eq_connectedComponentIn ht,D.openRegion_eq_connectedComponentIn ht,
    C.cellPoint_half_eq_center,D.cellPoint_half_eq_center,C.center_of_corners D hc]

def PennyGraph.rhombicFaces {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : Finset (BoundedFace G) := by
  classical
  exact Finset.univ.image (rhombusFaceMap G ht)

def PennyGraph.defectFaces {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : Finset (BoundedFace G) := by
  classical
  exact Finset.univ \ G.rhombicFaces ht

def PennyGraph.faceDefectCount {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : ℕ :=
  (G.defectFaces ht).card

theorem PennyGraph.rhombicFaces_card {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    (G.rhombicFaces ht).card=Fintype.card (RhombusSet G) := by
  classical
  rw [PennyGraph.rhombicFaces,Finset.card_image_of_injective _ (rhombusFaceMap_injective G ht),Finset.card_univ]

theorem PennyGraph.bounded_face_partition {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Fintype.card (BoundedFace G)=Fintype.card (RhombusSet G)+G.faceDefectCount ht := by
  classical
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (G.rhombicFaces ht))
  simpa only [PennyGraph.faceDefectCount,PennyGraph.defectFaces,G.rhombicFaces_card ht,
    Finset.card_univ,Nat.add_comm] using h.symm

def PennyGraph.FaceEuler {n : ℕ} (G : PennyGraph n) : Prop :=
  (n : ℤ)-G.edgeCount+Fintype.card (BoundedFace G)=1

theorem PennyGraph.euler_with_defects {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (he : G.FaceEuler) :
    (n : ℤ)-G.edgeCount+(Fintype.card (RhombusSet G)+G.faceDefectCount ht)=1 := by
  have hp : (Fintype.card (BoundedFace G) : ℤ)=
      (Fintype.card (RhombusSet G) : ℤ)+G.faceDefectCount ht := by
    exact_mod_cast G.bounded_face_partition ht
  change (n : ℤ)-G.edgeCount+Fintype.card (BoundedFace G)=1 at he
  rwa [hp] at he

end Swanepoel
