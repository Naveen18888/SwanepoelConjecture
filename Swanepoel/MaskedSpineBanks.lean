module
public import Swanepoel.HalfPieceBanks
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem RhombusCell.closedRegion_disjoint_other_spine {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (C : RhombusCell G) (cut : TrackComponent G)
    (hAB : edgeComponent C.edgeAB≠cut) (hAD : edgeComponent C.edgeAD≠cut) :
    Disjoint C.closedRegion (trackSpineTrace cut) := by
  apply Set.disjoint_left.mpr
  intro z hz hspine
  rcases track_spine_point_cases ht cut hspine with ⟨e,he,rfl⟩ | ⟨D,hD,hzD,_⟩
  · have hnot : edgeCenter e∉C.openRegion := by
      intro ho
      exact C.openRegion_subset_complement ht ho (G.edgeCenter_mem_drawing e)
    have hb := (C.closedRegion_subset_open_union_boundary ht hz).resolve_left hnot
    obtain ⟨E,hcorners,hE⟩ := C.align_edge_of_midpoint_mem_boundary e
      (by simpa only [edgeCenter_eq_midpoint] using hb)
    have ha : e.val.1∈C.corners := by rw [hE,← hcorners]; simp [RhombusCell.corners]
    have hb : e.val.2∈C.corners := by rw [hE,← hcorners]; simp [RhombusCell.corners]
    rcases C.inside_component ht e ha hb with h | h
    · exact hAB (h.symm.trans he)
    · exact hAD (h.symm.trans he)
  · have hnot : z∉C.boundary := by
      intro hb
      exact D.openRegion_subset_complement ht hzD (C.boundary_subset_drawing hb)
    have hzC := (C.closedRegion_subset_open_union_boundary ht hz).resolve_right hnot
    have hfaces : D.openRegion=C.openRegion :=
      ((D.isBoundedFace ht).1.eq_component hzD).trans ((C.isBoundedFace ht).1.eq_component hzC).symm
    have hc := D.corners_eq_of_openRegion_eq ht C hfaces
    have ha : D.a∈C.corners := by rw [← hc]; simp [RhombusCell.corners]
    have hb : D.b∈C.corners := by rw [← hc]; simp [RhombusCell.corners]
    rcases C.inside_component ht D.edgeAB ha hb with h | h
    · exact hAB (h.symm.trans hD)
    · exact hAD (h.symm.trans hD)

theorem TrackCutStep.other_component_ne {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} {e f : OrientedEdge G}
    (hstep : TrackCutStep cut e f) (C : RhombusCell G)
    (hE : e.val=(C.a,C.b)) (hF : f.val=(C.d,C.c)) : edgeComponent C.edgeAD≠cut := by
  obtain ⟨q,hq,hnot⟩ := hstep
  have heq : q.val.1=C.edgeAB := Subtype.ext (by
    change q.val.1.val=(C.a,C.b)
    simpa only [hq] using hE)
  have hfq : q.val.2=C.edgeDC := Subtype.ext (by
    change q.val.2.val=(C.d,C.c)
    simpa only [hq] using hF)
  have hc : q.rhombus.representative.corners=C.corners := by
    rw [q.rhombus.representative_corners]
    change stepCorners q.val.1 q.val.2=C.corners
    rw [heq,hfq,C.stepCorners_eq]
  intro he
  apply hnot
  have hp := q.rhombus.representative.trackPair_of_corners ht C hc
  change s(edgeComponent q.rhombus.representative.edgeAB,edgeComponent q.rhombus.representative.edgeAD)=
    s(edgeComponent C.edgeAB,edgeComponent C.edgeAD) at hp
  rcases Sym2.eq_iff.mp hp with h | h
  · exact Or.inr (h.2.trans he)
  · exact Or.inl (h.1.trans he)

inductive MaskedSpineChain {n : ℕ} (G : PennyGraph n) (cut : TrackComponent G) :
    OrientedEdge G → OrientedEdge G → Type
  | nil (s : OrientedEdge G) : MaskedSpineChain G cut s s
  | cons (s e t : OrientedEdge G) (step : TrackCutStep cut s e)
      (tail : MaskedSpineChain G cut e t) : MaskedSpineChain G cut s t

namespace MaskedSpineChain
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G}

def positive {s t : OrientedEdge G} : MaskedSpineChain G cut s t → PositiveSpineChain G s t
  | .nil s => .nil s
  | .cons s e t h p => .cons s e t h.to_positive p.positive

theorem exists_of_reach {s t : OrientedEdge G}
    (h : Relation.ReflTransGen (TrackCutStep cut) s t) : Nonempty (MaskedSpineChain G cut s t) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil _⟩
  | @head s e hse het ih =>
    obtain ⟨p⟩ := ih
    exact ⟨.cons s e _ hse p⟩

theorem translated_trace_avoids_cut {s t : OrientedEdge G}
    (p : MaskedSpineChain G cut s t) (ht : G.TriangleFree) (hne : edgeComponent s≠cut)
    {z : Plane} (hz : z∈p.positive.toPlane.trace) {δ : ℝ} (hδ : |δ|≤1/2) :
    z+δ • carriedVector s∉trackSpineTrace cut := by
  induction p with
  | nil s =>
    rw [Set.mem_singleton_iff.mp hz]
    have he : edgeCenter s+δ • carriedVector s∈G.edgeTrace s.val.1 s.val.2 := by
      have heq : edgeCenter s+δ • carriedVector s=G.edgePoint s.val.1 s.val.2 (1/2+δ) := by
        dsimp [edgeCenter,RhombusCell.midpoint2,carriedVector,PennyGraph.edgePoint]
        module
      have hh := abs_le.mp hδ
      exact ⟨1/2+δ,⟨by linarith,by linarith⟩,heq.symm⟩
    exact Set.disjoint_left.mp (edgeTrace_disjoint_other_spine ht s cut hne) he
  | cons s e t h p ih =>
    rcases hz with hz | hz
    · obtain ⟨C,hE,hF,hpos⟩ := h.to_positive
      have hnAB : edgeComponent C.edgeAB≠cut := by
        have heq : s=C.edgeAB := Subtype.ext hE
        simpa only [heq] using hne
      have hnAD := h.other_component_ne ht C hE hF
      have hzC : z+δ • carriedVector s∈C.closedRegion := by
        rw [segment_eq_image] at hz
        obtain ⟨r,hr,rfl⟩ := hz
        have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
          (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
        have heq : (1-r) • edgeCenter s+r • edgeCenter e+δ • carriedVector s=
            C.cellPoint (1/2+δ) r := by
          simp only [edgeCenter,hE,hF,carriedVector,RhombusCell.midpoint2,
            RhombusCell.cellPoint,RhombusCell.u,RhombusCell.v]
          rw [hc]
          module
        change (1-r) • edgeCenter s+r • edgeCenter e+δ • carriedVector s∈C.closedRegion
        rw [heq]
        have hh := abs_le.mp hδ
        exact ⟨by rw [C.coordU_cellPoint ht]; linarith,
          by rw [C.coordU_cellPoint ht]; linarith,
          by rw [C.coordV_cellPoint ht]; exact hr.1,
          by rw [C.coordV_cellPoint ht]; exact hr.2⟩
      exact Set.disjoint_left.mp (C.closedRegion_disjoint_other_spine ht cut hnAB hnAD) hzC
    · rw [h.to_positive.to_cellStep.vector_eq]
      apply ih (by rwa [← positive_path_component (Relation.ReflTransGen.single h.to_positive)]) hz

theorem bankRegion_avoids_two_spine_loop {s t finish : OrientedEdge G}
    (p : MaskedSpineChain G cut s t) (ht : G.TriangleFree)
    (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep finish g)
    (hfull : Relation.ReflTransGen PositiveCellStep s finish) (hne : edgeComponent s≠cut)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆(trackSpineTrace (edgeComponent s)∪trackSpineTrace cut)∪outer.val)
    (sign : ℝ) (hsign : sign=1 ∨ sign= -1) :
    Disjoint (p.positive.bankRegion sign) loop.trace := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,δ,hδ,rfl⟩ hz
  have hn : sign*δ≠0 := by rcases hsign with rfl | rfl <;> nlinarith [hδ.1]
  have hb : |sign*δ|≤1/2 := by
    rcases hsign with rfl | rfl <;> simp only [one_mul,neg_mul,abs_neg,abs_of_pos hδ.1] <;> exact hδ.2
  rcases hloop hz with (hv | hu) | hout
  · exact complete_spine_translated_point_not_on_spine ht hs htop hfull
      (p.positive.trace_subset_track hx) hn hv
  · exact p.translated_trace_avoids_cut ht hne hx hb hu
  · exact p.positive.translated_trace_avoids_outer ht outer houter hx hb hout

end MaskedSpineChain
end Swanepoel
