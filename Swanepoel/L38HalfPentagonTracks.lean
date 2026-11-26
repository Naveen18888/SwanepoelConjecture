module
public import Swanepoel.L38HalfPentagonEmbedding
public import Swanepoel.L38HalfGraph
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def halfPentagonEmbedding (side : Bool) : L38HalfPentagonEmbedding (B.halfGraph side) G where
  vertex := B.halfVertex side
  injective := B.halfVertex_injective side
  point_eq := B.halfGraph_point side

theorem halfPentagonEmbedding_edge (side : Bool) (e : OrientedEdge (B.halfGraph side)) :
    (B.halfPentagonEmbedding side).mapEdge e=B.halfEdge side e := rfl

def halfComponentMap (side : Bool) : TrackComponent (B.halfGraph side)→TrackComponent G :=
  (B.halfPentagonEmbedding side).componentMap

theorem halfComponentMap_edge (side : Bool) (e : OrientedEdge (B.halfGraph side)) :
    B.halfComponentMap side (edgeComponent e)=edgeComponent (B.halfEdge side e) := rfl

theorem halfComponentMap_crossing (side : Bool) {c d : TrackComponent (B.halfGraph side)}
    (h : ComponentCrosses c d) : ComponentCrosses (B.halfComponentMap side c) (B.halfComponentMap side d) :=
  (B.halfPentagonEmbedding side).crossing_map h

theorem half_source_of_old (side : Bool) (e : OrientedEdge (B.halfGraph side))
    (hs : SpineSource (B.halfEdge side e)) : SpineSource e :=
  (B.halfPentagonEmbedding side).source_of_source_map e hs

theorem liftHalfEdge_source (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∈B.bankVertices side) (hb : e.val.2∈B.bankVertices side) (hs : SpineSource e) :
    SpineSource (B.liftHalfEdge side e ha hb) := by
  apply B.half_source_of_old side
  simpa only [B.halfEdge_lift] using hs

theorem half_positive_step_iff (ht : G.TriangleFree) (side : Bool)
    (e f : OrientedEdge (B.halfGraph side)) :
    PositiveCellStep e f↔TrackCutStep cut (B.halfEdge side e) (B.halfEdge side f) := by
  constructor
  · intro h
    obtain ⟨C,he,hf,hpos⟩ := h
    let E := B.halfPentagonEmbedding side
    have hmap : PositiveCellStep (B.halfEdge side e) (B.halfEdge side f) :=
      (E.positive_step_iff e f).mp ⟨C,he,hf,hpos⟩
    let q : SpineTransition G := ⟨(B.halfEdge side e,B.halfEdge side f),hmap⟩
    refine ⟨q,rfl,?_⟩
    intro hcut
    have hAD := q.other_component_eq_cut ht cut hcut (B.halfEdge_ne_cut ht side e) (E.mapCell C)
      (congrArg (Prod.map E.vertex E.vertex) he) (congrArg (Prod.map E.vertex E.vertex) hf)
    exact B.halfEdge_ne_cut ht side C.edgeAD hAD
  · intro h
    exact ((B.halfPentagonEmbedding side).positive_step_iff e f).mpr h.to_positive

theorem half_positive_path_masked (ht : G.TriangleFree) (side : Bool)
    {e f : OrientedEdge (B.halfGraph side)} (h : Relation.ReflTransGen PositiveCellStep e f) :
    Relation.ReflTransGen (TrackCutStep cut) (B.halfEdge side e) (B.halfEdge side f) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.tail ((B.half_positive_step_iff ht side _ _).mp h)

theorem bank_edge_ne_cut (ht : G.TriangleFree) (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∈B.bankVertices side) (hb : e.val.2∈B.bankVertices side) : edgeComponent e≠cut := by
  intro h
  exact B.cut_vertexBankCode_ne ht e h
    (((B.mem_bankVertices side _).mp ha).trans ((B.mem_bankVertices side _).mp hb).symm)

theorem masked_step_vertices_mem (ht : G.TriangleFree) (side : Bool)
    {e f : OrientedEdge G} (h : TrackCutStep cut e f)
    (ha : e.val.1∈B.bankVertices side) (hb : e.val.2∈B.bankVertices side) :
    f.val.1∈B.bankVertices side ∧ f.val.2∈B.bankVertices side := by
  have hne := B.bank_edge_ne_cut ht side e ha hb
  have hcomp := (positive_path_component (Relation.ReflTransGen.single h.to_positive)).symm
  have hlabels := h.start_vertex_winding_eq ht cut B.outer B.loop B.support
  change B.vertexLabel e.val.1=B.vertexLabel f.val.1 at hlabels
  have hcode : B.vertexBankCode f.val.1=side := by
    change decide (B.vertexLabel f.val.1=B.positiveLabel)=side
    rw [← hlabels]
    exact (B.mem_bankVertices side _).mp ha
  have hends := B.noncut_vertexBankCode_eq ht f (hcomp ▸ hne)
  exact ⟨(B.mem_bankVertices side _).mpr hcode,(B.mem_bankVertices side _).mpr (hends.symm.trans hcode)⟩

theorem lift_masked_path (ht : G.TriangleFree) (side : Bool)
    {e f : OrientedEdge G} (ha : e.val.1∈B.bankVertices side) (hb : e.val.2∈B.bankVertices side)
    (h : Relation.ReflTransGen (TrackCutStep cut) e f) :
    ∃ hfa : f.val.1∈B.bankVertices side,∃ hfb : f.val.2∈B.bankVertices side,
      Relation.ReflTransGen PositiveCellStep (B.liftHalfEdge side e ha hb) (B.liftHalfEdge side f hfa hfb) := by
  induction h with
  | refl => exact ⟨ha,hb,Relation.ReflTransGen.refl⟩
  | @tail f g hpath hstep ih =>
    obtain ⟨hfa,hfb,hchain⟩ := ih
    obtain ⟨hga,hgb⟩ := B.masked_step_vertices_mem ht side hstep hfa hfb
    refine ⟨hga,hgb,hchain.tail ?_⟩
    apply (B.half_positive_step_iff ht side _ _).mpr
    simpa only [B.halfEdge_lift] using hstep

theorem half_source_iff_no_masked_predecessor (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) :
    SpineSource e↔¬∃ f : OrientedEdge G,TrackCutStep cut f (B.halfEdge side e) := by
  constructor
  · intro hs
    rintro ⟨f,hf⟩
    have ha := B.halfVertex_mem side e.val.1
    have hb := B.halfVertex_mem side e.val.2
    obtain ⟨hfb,hfa⟩ := B.masked_step_vertices_mem ht side hf.reverse hb ha
    have hp : PositiveCellStep (B.liftHalfEdge side f hfa hfb) e := by
      apply (B.half_positive_step_iff ht side _ _).mpr
      rw [B.halfEdge_lift side f hfa hfb]
      exact hf
    exact hs ⟨_,hp⟩
  · intro hs
    rintro ⟨f,hf⟩
    exact hs ⟨B.halfEdge side f,(B.half_positive_step_iff ht side _ _).mp hf⟩

theorem half_source_old_or_cut (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) (hs : SpineSource e) :
    SpineSource (B.halfEdge side e) ∨
      ∃ q : SpineTransition G,q.val.2=B.halfEdge side e ∧ cutRhombus cut q.rhombus := by
  by_cases hold : SpineSource (B.halfEdge side e)
  · exact Or.inl hold
  · right
    obtain ⟨f,hf⟩ := not_not.mp hold
    let q : SpineTransition G := ⟨(f,B.halfEdge side e),hf⟩
    refine ⟨q,rfl,?_⟩
    by_contra hn
    exact ((B.half_source_iff_no_masked_predecessor ht side e).mp hs) ⟨f,q,rfl,hn⟩

theorem half_full_component_retained (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) (hs : SpineSource (B.halfEdge side e))
    (hmiss : ¬ComponentCrosses (edgeComponent (B.halfEdge side e)) cut) :
    ∀ a : OrientedEdge G,edgeComponent a=edgeComponent (B.halfEdge side e) →
      ∃ b : OrientedEdge (B.halfGraph side),B.halfEdge side b=a := by
  intro a hcomp
  have hne := B.halfEdge_ne_cut ht side e
  have hl := B.noncrossing_carried_vertex_label ht (B.halfEdge side e) a hs hcomp hne hmiss
  have hcode : B.vertexBankCode a.val.1=side := by
    change decide (B.vertexLabel a.val.1=B.positiveLabel)=side
    rw [hl]
    exact (B.mem_bankVertices side _).mp (B.halfVertex_mem side e.val.1)
  have hends := B.noncut_vertexBankCode_eq ht a (hcomp ▸ hne)
  let ha := (B.mem_bankVertices side _).mpr hcode
  let hb := (B.mem_bankVertices side _).mpr (hends.symm.trans hcode)
  exact ⟨B.liftHalfEdge side a ha hb,B.halfEdge_lift side a ha hb⟩

theorem half_edge_piece_bank_code (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) :
    B.cutPieceBankCode ht (trackCutComponent cut (B.halfEdge side e))=side := by
  change B.vertexBankCode (B.halfEdge side e).val.1=side
  exact (B.mem_bankVertices side _).mp (B.halfVertex_mem side e.val.1)

theorem half_component_eq_of_old_source (ht : G.TriangleFree) (side : Bool)
    (e f : OrientedEdge (B.halfGraph side)) (hs : SpineSource (B.halfEdge side e))
    (hc : edgeComponent (B.halfEdge side f)=edgeComponent (B.halfEdge side e)) :
    edgeComponent e=edgeComponent f := by
  by_cases hx : ComponentCrosses (edgeComponent (B.halfEdge side e)) cut
  · have hne := B.halfEdge_ne_cut ht side e
    obtain ⟨q,hqcut,hprefix,hpairs⟩ := crossing_cut_transition_before_source ht cut (B.halfEdge side e) hs hne hx
    obtain ⟨s,t,hs',htop,hE,hall⟩ := component_spine_iff ht (B.halfEdge side e)
    have hse : s=B.halfEdge side e := source_path_eq hs hE.1
    subst s
    have hfull := hE.1.trans hE.2
    have hq : OnSpine (B.halfEdge side e) t q.val.1 :=
      (onSpine_positive_path_iff ht hs htop hprefix).mp ⟨Relation.ReflTransGen.refl,hfull⟩
    have hsuffix := spine_suffix_closed ht htop hq.2 q.property
    have connect (a : OrientedEdge (B.halfGraph side))
        (ha : OnSpine (B.halfEdge side e) t (B.halfEdge side a)) : edgeComponent e=edgeComponent a := by
      have hbefore := B.same_bank_onSpine_before_cut ht side hs htop q hqcut hpairs hprefix hsuffix ha hne
        (B.half_edge_piece_bank_code ht side e) (B.half_edge_piece_bank_code ht side a)
      obtain ⟨hqa,hqb,hep⟩ := B.lift_masked_path ht side (B.halfVertex_mem side e.val.1)
        (B.halfVertex_mem side e.val.2) (path_before_global_cut_preserved cut q hpairs hprefix)
      obtain ⟨hqa',hqb',hap⟩ := B.lift_masked_path ht side (B.halfVertex_mem side a.val.1)
        (B.halfVertex_mem side a.val.2) (path_before_global_cut_preserved cut q hpairs hbefore.2)
      have heLift : B.liftHalfEdge side (B.halfEdge side e) (B.halfVertex_mem side e.val.1)
          (B.halfVertex_mem side e.val.2)=e := B.halfEdge_injective side (B.halfEdge_lift side _ _ _)
      have haLift : B.liftHalfEdge side (B.halfEdge side a) (B.halfVertex_mem side a.val.1)
          (B.halfVertex_mem side a.val.2)=a := B.halfEdge_injective side (B.halfEdge_lift side _ _ _)
      have hep' := positive_path_component hep
      have hap' := positive_path_component hap
      rw [heLift] at hep'
      rw [haLift] at hap'
      exact hep'.trans hap'.symm
    rcases (hall (B.halfEdge side f)).mp hc with hf | hf
    · exact connect f hf
    · have hfr : OnSpine (B.halfEdge side e) t (B.halfEdge side (reverseEdge f)) :=
        onSpine_reverse_iff.mp hf
      exact (connect (reverseEdge f) hfr).trans (reverse_component f).symm
  · apply (B.halfPentagonEmbedding side).component_eq_of_full_retention e f hc.symm
    exact B.half_full_component_retained ht side e hs hx

theorem half_old_source_components_eq (ht : G.TriangleFree) (side : Bool)
    (e f : OrientedEdge (B.halfGraph side))
    (he : SpineSource (B.halfEdge side e)) (hf : SpineSource (B.halfEdge side f))
    (heB : G.sourceFace (B.halfEdge side e)∈B.bankDefectFamily ht side)
    (hfB : G.sourceFace (B.halfEdge side f)∈B.bankDefectFamily ht side)
    (hc : edgeComponent (B.halfEdge side e)=edgeComponent (B.halfEdge side f)) :
    edgeComponent e=edgeComponent f := by
  by_cases hx : ComponentCrosses (edgeComponent (B.halfEdge side e)) cut
  · have hef := B.crossing_bank_sources_eq ht side (B.halfEdge side e) (B.halfEdge side f) he hf heB hfB hc.symm hx
    exact congrArg edgeComponent (B.halfEdge_injective side hef)
  · apply (B.halfPentagonEmbedding side).component_eq_of_full_retention e f hc
    exact B.half_full_component_retained ht side e he hx

end OrdinaryCutBanks
end Swanepoel
