module
public import Swanepoel.TerminalPortConservation
public import Swanepoel.SemicirclePorts
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def trackDisplacement {n : ℕ} {G : PennyGraph n}
    (w : TrackComponent G → ℝ) (e : OrientedEdge G) : Plane :=
  w (edgeComponent e) • carriedVector e

def retainedDisplacement {n : ℕ} {G : PennyGraph n}
    (A : Finset (TrackComponent G)) (e : OrientedEdge G) : Plane :=
  trackDisplacement (fun c => if c∈A then 1 else 0) e

theorem trackDisplacement_reverse {n : ℕ} {G : PennyGraph n}
    (w : TrackComponent G → ℝ) (e : OrientedEdge G) :
    trackDisplacement w (reverseEdge e)= -trackDisplacement w e := by
  unfold trackDisplacement
  rw [← reverse_component e,reverseEdge_vector,smul_neg]

theorem CellStep.trackDisplacement_eq {n : ℕ} {G : PennyGraph n}
    {e f : OrientedEdge G} (h : CellStep e f) (w : TrackComponent G → ℝ) :
    trackDisplacement w e=trackDisplacement w f := by
  have hc : edgeComponent e=edgeComponent f :=
    Quotient.sound (Relation.EqvGen.rel _ _ (Or.inl h))
  unfold trackDisplacement
  rw [hc,h.vector_eq]

theorem retainedDisplacement_of_mem {n : ℕ} {G : PennyGraph n}
    (A : Finset (TrackComponent G)) (e : OrientedEdge G) (he : edgeComponent e∈A) :
    retainedDisplacement A e=carriedVector e := by
  simp [retainedDisplacement,trackDisplacement,he]

theorem retainedDisplacement_of_notMem {n : ℕ} {G : PennyGraph n}
    (A : Finset (TrackComponent G)) (e : OrientedEdge G) (he : edgeComponent e∉A) :
    retainedDisplacement A e=0 := by
  simp [retainedDisplacement,trackDisplacement,he]

theorem retainedDisplacement_norm_le_one {n : ℕ} {G : PennyGraph n}
    (A : Finset (TrackComponent G)) (e : OrientedEdge G) :
    ‖retainedDisplacement A e‖≤1 := by
  by_cases he : edgeComponent e∈A
  · rw [retainedDisplacement_of_mem A e he,carriedVector_norm]
  · rw [retainedDisplacement_of_notMem A e he,norm_zero]
    norm_num

theorem RhombusCell.trackDisplacement_boundary_sum {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (w : TrackComponent G → ℝ) :
    trackDisplacement w C.edgeAB+trackDisplacement w C.edgeBC+
      trackDisplacement w C.edgeCD+trackDisplacement w C.edgeDA=0 := by
  have hcd : C.edgeCD=reverseEdge C.edgeDC := by apply Subtype.ext; rfl
  have hda : C.edgeDA=reverseEdge C.edgeAD := by apply Subtype.ext; rfl
  have hdc := (show CellStep C.edgeAB C.edgeDC from ⟨C,rfl,rfl⟩).trackDisplacement_eq w
  have hbc := (show CellStep C.edgeAD C.edgeBC from
    ⟨C.transpose,rfl,rfl⟩).trackDisplacement_eq w
  rw [hcd,hda,trackDisplacement_reverse,trackDisplacement_reverse,← hdc,← hbc]
  abel

theorem RhombusCell.retainedDisplacement_boundary_sum {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (A : Finset (TrackComponent G)) :
    retainedDisplacement A C.edgeAB+retainedDisplacement A C.edgeBC+
      retainedDisplacement A C.edgeCD+retainedDisplacement A C.edgeDA=0 :=
  C.trackDisplacement_boundary_sum _

theorem RhombusCell.trackDisplacement_det {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (w : TrackComponent G → ℝ) :
    cross2 (trackDisplacement w C.edgeAB) (trackDisplacement w C.edgeAD)=
      w (edgeComponent C.edgeAB)*w (edgeComponent C.edgeAD)*cross2 C.u C.v := by
  unfold trackDisplacement
  rw [cross2_smul_left,cross2_smul_right]
  change _*( _*cross2 C.u C.v)=_
  ring

theorem RhombusCell.retainedDisplacement_area {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (A : Finset (TrackComponent G)) :
    |cross2 (retainedDisplacement A C.edgeAB) (retainedDisplacement A C.edgeAD)|=
      if edgeComponent C.edgeAB∈A ∧ edgeComponent C.edgeAD∈A then |cross2 C.u C.v| else 0 := by
  rw [retainedDisplacement,retainedDisplacement,C.trackDisplacement_det]
  by_cases hA : edgeComponent C.edgeAB∈A <;>
    by_cases hB : edgeComponent C.edgeAD∈A <;> simp [hA,hB]

theorem RhombusCell.retainedDisplacement_area_lower {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (A : Finset (TrackComponent G))
    (ha : edgeComponent C.edgeAB∈A) (hb : edgeComponent C.edgeAD∈A) :
    Real.sqrt 3/2 < |cross2 (retainedDisplacement A C.edgeAB)
      (retainedDisplacement A C.edgeAD)| := by
  rw [C.retainedDisplacement_area A,ite_eq_left ⟨ha,hb⟩]
  exact C.area_lower ht

theorem PennyGraph.terminal_displacement_on_defect_edge {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (e : OrientedEdge G) (he : G.sourceFace e=F) :
    retainedDisplacement G.terminalTrackComponents e=carriedVector e := by
  apply retainedDisplacement_of_mem
  have hs := G.spineSource_of_sourceFace_mem_defects ht e (he ▸ hF)
  apply G.defect_source_port_terminal ht hF
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs,he⟩

theorem PennyGraph.terminal_displacement_defect_walk_sum {n k : ℕ}
    (G : PennyGraph n) (ht : G.TriangleFree) (F : PlaneFace G)
    (hF : F∈G.defectPlaneFaces ht) (vertices : Fin (k+1) → Fin n)
    (edges : Fin k → OrientedEdge G)
    (hstart : ∀ i, (edges i).val.1=vertices i.castSucc)
    (hend : ∀ i, (edges i).val.2=vertices i.succ)
    (hclosed : vertices (Fin.last k)=vertices 0)
    (hface : ∀ i, G.sourceFace (edges i)=F) :
    (∑ i, retainedDisplacement G.terminalTrackComponents (edges i))=0 := by
  have heq (i : Fin k) : retainedDisplacement G.terminalTrackComponents (edges i)=
      G.point (vertices i.succ)-G.point (vertices i.castSucc) := by
    rw [G.terminal_displacement_on_defect_edge ht F hF (edges i) (hface i)]
    simp only [carriedVector,hstart,hend]
  simp_rw [heq]
  rw [polygon_edge_sum (fun i => G.point (vertices i)),hclosed,sub_self]

end Swanepoel
