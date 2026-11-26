module
public import Swanepoel.SpokePairWinding
public import Swanepoel.HalfBankSeparation
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem PositiveSpineChain.translated_trace_avoids_defect {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    {z : Plane} (hz : z∈p.toPlane.trace) {δ : ℝ} (hδ : |δ|≤1/2) :
    z+δ • carriedVector s∉F.val := by
  intro hface
  rcases p.translated_trace_in_drawing_or_cell ht hz hδ with hdraw | ⟨C,hC⟩
  · exact G.face_subset_complement F hface hdraw
  · exact Set.disjoint_left.mp (G.defectFace_disjoint_closedRhombus ht F hF C) hface hC

theorem PositiveSpineChain.exists_noncrossing_mask {n : ℕ} {G : PennyGraph n}
    {s t : OrientedEdge G} (p : PositiveSpineChain G s t) :
    ∀ (_ht : G.TriangleFree) (cut : TrackComponent G), edgeComponent s≠cut →
      ¬ComponentCrosses (edgeComponent s) cut →
      ∃ q : MaskedSpineChain G cut s t,q.positive=p := by
  induction p with
  | nil s => intro _ht cut hne hmiss; exact ⟨.nil s,rfl⟩
  | cons s e t h tail ih =>
    intro ht cut hne hmiss
    have hcomp := positive_path_component (Relation.ReflTransGen.single h)
    obtain ⟨q,hq⟩ := ih ht cut (by rwa [← hcomp]) (by rwa [← hcomp])
    refine ⟨.cons s e t (noncrossing_step_preserved ht hne hmiss h) q,?_⟩
    change PositiveSpineChain.cons s e t h q.positive=PositiveSpineChain.cons s e t h tail
    rw [hq]

theorem PositiveSpineChain.translated_trace_avoids_noncrossing_spine {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (cut : TrackComponent G) (hne : edgeComponent s≠cut)
    (hmiss : ¬ComponentCrosses (edgeComponent s) cut)
    {z : Plane} (hz : z∈p.toPlane.trace) {δ : ℝ} (hδ : |δ|≤1/2) :
    z+δ • carriedVector s∉trackSpineTrace cut := by
  obtain ⟨q,hq⟩ := p.exists_noncrossing_mask ht cut hne hmiss
  exact q.translated_trace_avoids_cut ht hne (hq ▸ hz) hδ

theorem PositiveSpineChain.bankRegion_avoids_spoke_pair_loop {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    (cut : TrackComponent G) (hne : edgeComponent s≠cut)
    (hmiss : ¬ComponentCrosses (edgeComponent s) cut)
    (F outer : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (houter : ¬Bornology.IsBounded outer.val) {a : Plane} (loop : PlaneChain a a)
    (hloop : G.SpokePairSupport (edgeComponent s) cut F outer loop)
    (sign : ℝ) (hsign : sign=1 ∨ sign= -1) : Disjoint (p.bankRegion sign) loop.trace := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,δ,hδ,rfl⟩ hz
  have hn : sign*δ≠0 := by rcases hsign with rfl | rfl <;> nlinarith [hδ.1]
  have hb : |sign*δ|≤1/2 := by
    rcases hsign with rfl | rfl <;> simp only [one_mul,neg_mul,abs_neg,abs_of_pos hδ.1] <;> exact hδ.2
  rcases hloop hz with ((hown | hother) | hface) | hout
  · exact complete_spine_translated_point_not_on_spine ht hs htop p.reach (p.trace_subset_track hx) hn hown
  · exact p.translated_trace_avoids_noncrossing_spine ht cut hne hmiss hx hb hother
  · exact p.translated_trace_avoids_defect ht F hF hx hb hface
  · exact p.translated_trace_avoids_outer ht outer houter hx hb hout

end Swanepoel
