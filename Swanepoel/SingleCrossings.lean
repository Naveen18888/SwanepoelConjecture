module
public import Swanepoel.SpineMidpoints
@[expose] public section

noncomputable section
namespace Swanepoel

def RhombusCell.edgeDC {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : OrientedEdge G :=
  ⟨(C.d,C.c),C.cd.symm⟩

def RhombusCell.center {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : Plane :=
  RhombusCell.midpoint2 (G.point C.a) (G.point C.c)

def RhombusCell.corners {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : Finset (Fin n) :=
  {C.a,C.b,C.c,C.d}

def stepCorners {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) : Finset (Fin n) :=
  {e.val.1,e.val.2,f.val.1,f.val.2}

theorem stepCorners_comm {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) :
    stepCorners e f=stepCorners f e := by
  ext i
  simp only [stepCorners,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem stepCorners_reverseSwap {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) :
    stepCorners (reverseEdge f) (reverseEdge e)=stepCorners e f := by
  ext i
  simp only [stepCorners,reverseEdge,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem RhombusCell.stepCenter_eq {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    stepCenter C.edgeAB C.edgeDC=C.center := by
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  dsimp [stepCenter,edgeCenter,RhombusCell.midpoint2,RhombusCell.edgeAB,
    RhombusCell.edgeDC,RhombusCell.center]
  rw [hc]
  module

theorem RhombusCell.stepCorners_eq {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    stepCorners C.edgeAB C.edgeDC=C.corners := by
  ext i
  simp only [stepCorners,RhombusCell.edgeAB,RhombusCell.edgeDC,RhombusCell.corners,
    Finset.mem_insert,Finset.mem_singleton]
  tauto

def CellSpineWitness {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) (t : TrackComponent G) : Prop :=
  ∃ e f, PositiveCellStep e f ∧ edgeComponent e=t ∧
    stepCenter e f=C.center ∧ stepCorners e f=C.corners

theorem RhombusCell.spineWitness_ab {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (ht : G.TriangleFree) : CellSpineWitness C (edgeComponent C.edgeAB) := by
  have hc : CellStep C.edgeAB C.edgeDC := ⟨C,rfl,rfl⟩
  rcases cellStep_oriented ht hc with h | h
  · exact ⟨C.edgeAB,C.edgeDC,h,rfl,C.stepCenter_eq,C.stepCorners_eq⟩
  · refine ⟨C.edgeDC,C.edgeAB,h,positive_path_component (.single h),?_,?_⟩
    · rw [stepCenter_comm]
      exact C.stepCenter_eq
    · rw [stepCorners_comm]
      exact C.stepCorners_eq

def RhombusCell.transpose {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : RhombusCell G where
  a := C.a
  b := C.d
  c := C.c
  d := C.b
  ac := C.ac
  bd := C.bd.symm
  ab := C.da.symm
  bc := C.cd.symm
  cd := C.bc.symm
  da := C.ab.symm

theorem RhombusCell.transpose_corners {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    C.transpose.corners=C.corners := by
  ext i
  simp only [RhombusCell.transpose,RhombusCell.corners,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem RhombusCell.spineWitness_ad {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (ht : G.TriangleFree) : CellSpineWitness C (edgeComponent C.edgeAD) := by
  obtain ⟨e,f,hpos,he,hcenter,hcorners⟩ := C.transpose.spineWitness_ab ht
  refine ⟨e,f,hpos,he,hcenter,?_⟩
  exact hcorners.trans C.transpose_corners

theorem RhombusCell.spineWitness {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (ht : G.TriangleFree) (t : TrackComponent G)
    (h : edgeComponent C.edgeAB=t ∨ edgeComponent C.edgeAD=t) : CellSpineWitness C t := by
  rcases h with h | h
  · rw [← h]
    exact C.spineWitness_ab ht
  · rw [← h]
    exact C.spineWitness_ad ht

theorem cell_witness_comparison {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {C D : RhombusCell G} {t : TrackComponent G}
    (hC : CellSpineWitness C t) (hD : CellSpineWitness D t) :
    C.corners=D.corners ∨ SharpNormal (componentVector t) (D.center-C.center) := by
  obtain ⟨e,f,hef,he,hce,hco⟩ := hC
  obtain ⟨g,k,hgk,hg,hcg,hgo⟩ := hD
  rcases component_step_centers ht hef hgk (he.trans hg.symm) with h | h | h
  · have hc : stepCorners e f=stepCorners g k := by rw [h.1,h.2]
    exact Or.inl (hco.symm.trans (hc.trans hgo))
  · have hc : stepCorners e f=stepCorners g k := by
      rw [h.1,h.2]
      exact stepCorners_reverseSwap g k
    exact Or.inl (hco.symm.trans (hc.trans hgo))
  · rw [hce,hcg] at h
    exact Or.inr (SharpNormal.sameLine (component_sameLine e t he) h)

theorem rhombi_single_crossing {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (C D : RhombusCell G) (t u : TrackComponent G)
    (hC : (edgeComponent C.edgeAB=t ∧ edgeComponent C.edgeAD=u) ∨
      (edgeComponent C.edgeAB=u ∧ edgeComponent C.edgeAD=t))
    (hD : (edgeComponent D.edgeAB=t ∧ edgeComponent D.edgeAD=u) ∨
      (edgeComponent D.edgeAB=u ∧ edgeComponent D.edgeAD=t)) : C.corners=D.corners := by
  have hCt : edgeComponent C.edgeAB=t ∨ edgeComponent C.edgeAD=t := by tauto
  have hCu : edgeComponent C.edgeAB=u ∨ edgeComponent C.edgeAD=u := by tauto
  have hDt : edgeComponent D.edgeAB=t ∨ edgeComponent D.edgeAD=t := by tauto
  have hDu : edgeComponent D.edgeAB=u ∨ edgeComponent D.edgeAD=u := by tauto
  rcases cell_witness_comparison ht (C.spineWitness ht t hCt) (D.spineWitness ht t hDt) with h | h
  · exact h
  rcases cell_witness_comparison ht (C.spineWitness ht u hCu) (D.spineWitness ht u hDu) with h' | h'
  · exact h'
  have hcross := component_crossing_angle ht (show ComponentCrosses t u from ⟨C,hC⟩)
  exact False.elim (no_common_sharpNormal _ _ _ (componentVector_norm t) (componentVector_norm u)
    hcross h h')

end Swanepoel
