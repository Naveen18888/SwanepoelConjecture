module
public import Swanepoel.L38PentagonFamilyCrossings
@[expose] public section

noncomputable section
namespace Swanepoel

structure L38HalfPentagonEmbedding {m n : ℕ} (H : PennyGraph m) (G : PennyGraph n) where
  vertex : Fin m→Fin n
  injective : Function.Injective vertex
  point_eq : ∀ v,H.point v=G.point (vertex v)

namespace L38HalfPentagonEmbedding
variable {m n : ℕ} {H : PennyGraph m} {G : PennyGraph n} (E : L38HalfPentagonEmbedding H G)

theorem adj_iff (a b : Fin m) : H.graph.Adj a b↔G.graph.Adj (E.vertex a) (E.vertex b) := by
  constructor
  · rintro ⟨hne,hd⟩
    exact ⟨fun h => hne (E.injective h),by rw [← E.point_eq,← E.point_eq]; exact hd⟩
  · rintro ⟨hne,hd⟩
    exact ⟨fun h => hne (congrArg E.vertex h),by rw [E.point_eq,E.point_eq]; exact hd⟩

def mapEdge (e : OrientedEdge H) : OrientedEdge G :=
  ⟨(E.vertex e.val.1,E.vertex e.val.2),(E.adj_iff _ _).mp e.property⟩

theorem mapEdge_injective : Function.Injective E.mapEdge := by
  intro e f h
  apply Subtype.ext
  exact Prod.ext (E.injective (congrArg (fun e : OrientedEdge G => e.val.1) h))
    (E.injective (congrArg (fun e : OrientedEdge G => e.val.2) h))

theorem mapEdge_reverse (e : OrientedEdge H) : E.mapEdge (reverseEdge e)=reverseEdge (E.mapEdge e) := by
  apply Subtype.ext
  rfl

theorem mapEdge_vector (e : OrientedEdge H) : carriedVector (E.mapEdge e)=carriedVector e := by
  change G.point (E.vertex e.val.2)-G.point (E.vertex e.val.1)=H.point e.val.2-H.point e.val.1
  rw [← E.point_eq,← E.point_eq]

theorem mapEdge_center (e : OrientedEdge H) : edgeCenter (E.mapEdge e)=edgeCenter e := by
  change RhombusCell.midpoint2 (G.point (E.vertex e.val.1)) (G.point (E.vertex e.val.2))=
    RhombusCell.midpoint2 (H.point e.val.1) (H.point e.val.2)
  rw [← E.point_eq,← E.point_eq]

theorem mapEdge_normal (e : OrientedEdge H) : sourceNormal (E.mapEdge e)=sourceNormal e := by
  unfold sourceNormal
  rw [E.mapEdge_vector]

def mapCell (C : RhombusCell H) : RhombusCell G where
  a := E.vertex C.a
  b := E.vertex C.b
  c := E.vertex C.c
  d := E.vertex C.d
  ac := fun h => C.ac (E.injective h)
  bd := fun h => C.bd (E.injective h)
  ab := (E.adj_iff _ _).mp C.ab
  bc := (E.adj_iff _ _).mp C.bc
  cd := (E.adj_iff _ _).mp C.cd
  da := (E.adj_iff _ _).mp C.da

theorem mapCell_u (C : RhombusCell H) : (E.mapCell C).u=C.u := by
  change G.point (E.vertex C.b)-G.point (E.vertex C.a)=H.point C.b-H.point C.a
  rw [← E.point_eq,← E.point_eq]

theorem mapCell_v (C : RhombusCell H) : (E.mapCell C).v=C.v := by
  change G.point (E.vertex C.d)-G.point (E.vertex C.a)=H.point C.d-H.point C.a
  rw [← E.point_eq,← E.point_eq]

def pullCell (e f : OrientedEdge H) (C : RhombusCell G)
    (he : (E.mapEdge e).val=(C.a,C.b)) (hf : (E.mapEdge f).val=(C.d,C.c)) : RhombusCell H where
  a := e.val.1
  b := e.val.2
  c := f.val.2
  d := f.val.1
  ac := by
    intro h
    apply C.ac
    calc
      C.a=E.vertex e.val.1 := (congrArg Prod.fst he).symm
      _=E.vertex f.val.2 := congrArg E.vertex h
      _=C.c := congrArg Prod.snd hf
  bd := by
    intro h
    apply C.bd
    calc
      C.b=E.vertex e.val.2 := (congrArg Prod.snd he).symm
      _=E.vertex f.val.1 := congrArg E.vertex h
      _=C.d := congrArg Prod.fst hf
  ab := e.property
  bc := (E.adj_iff _ _).mpr (by
    change G.graph.Adj (E.mapEdge e).val.2 (E.mapEdge f).val.2
    rw [he,hf]
    exact C.bc)
  cd := f.property.symm
  da := (E.adj_iff _ _).mpr (by
    change G.graph.Adj (E.mapEdge f).val.1 (E.mapEdge e).val.1
    rw [he,hf]
    exact C.da)

theorem pullCell_u (e f : OrientedEdge H) (C : RhombusCell G)
    (he : (E.mapEdge e).val=(C.a,C.b)) (hf : (E.mapEdge f).val=(C.d,C.c)) :
    (E.pullCell e f C he hf).u=C.u := by
  change H.point e.val.2-H.point e.val.1=G.point C.b-G.point C.a
  rw [E.point_eq,E.point_eq]
  change G.point (E.mapEdge e).val.2-G.point (E.mapEdge e).val.1=G.point C.b-G.point C.a
  rw [he]

theorem pullCell_v (e f : OrientedEdge H) (C : RhombusCell G)
    (he : (E.mapEdge e).val=(C.a,C.b)) (hf : (E.mapEdge f).val=(C.d,C.c)) :
    (E.pullCell e f C he hf).v=C.v := by
  change H.point f.val.1-H.point e.val.1=G.point C.d-G.point C.a
  rw [E.point_eq,E.point_eq]
  change G.point (E.mapEdge f).val.1-G.point (E.mapEdge e).val.1=G.point C.d-G.point C.a
  rw [he,hf]

theorem cell_step_iff (e f : OrientedEdge H) : CellStep e f↔CellStep (E.mapEdge e) (E.mapEdge f) := by
  constructor
  · rintro ⟨C,he,hf⟩
    refine ⟨E.mapCell C,?_,?_⟩
    · exact congrArg (Prod.map E.vertex E.vertex) he
    · exact congrArg (Prod.map E.vertex E.vertex) hf
  · rintro ⟨C,he,hf⟩
    exact ⟨E.pullCell e f C he hf,rfl,rfl⟩

theorem positive_step_iff (e f : OrientedEdge H) :
    PositiveCellStep e f↔PositiveCellStep (E.mapEdge e) (E.mapEdge f) := by
  constructor
  · rintro ⟨C,he,hf,hpos⟩
    refine ⟨E.mapCell C,congrArg (Prod.map E.vertex E.vertex) he,
      congrArg (Prod.map E.vertex E.vertex) hf,?_⟩
    rwa [E.mapCell_u,E.mapCell_v]
  · rintro ⟨C,he,hf,hpos⟩
    refine ⟨E.pullCell e f C he hf,rfl,rfl,?_⟩
    rwa [E.pullCell_u,E.pullCell_v]

theorem track_step_iff (e f : OrientedEdge H) :
    TrackStep e f↔TrackStep (E.mapEdge e) (E.mapEdge f) := by
  unfold TrackStep
  rw [← E.cell_step_iff,← E.mapEdge_reverse]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (congrArg E.mapEdge h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (E.mapEdge_injective h)

theorem map_track_relation {e f : OrientedEdge H} (h : Relation.EqvGen TrackStep e f) :
    Relation.EqvGen TrackStep (E.mapEdge e) (E.mapEdge f) := by
  induction h with
  | rel e f h => exact Relation.EqvGen.rel _ _ ((E.track_step_iff e f).mp h)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

def componentMap : TrackComponent H→TrackComponent G :=
  Quotient.map E.mapEdge (fun _ _ h => E.map_track_relation h)

theorem componentMap_edge (e : OrientedEdge H) :
    E.componentMap (edgeComponent e)=edgeComponent (E.mapEdge e) := rfl

theorem component_eq_of_full_retention (e f : OrientedEdge H)
    (hcomp : edgeComponent (E.mapEdge e)=edgeComponent (E.mapEdge f))
    (hretained : ∀ a : OrientedEdge G,edgeComponent a=edgeComponent (E.mapEdge e) →
      ∃ b : OrientedEdge H,E.mapEdge b=a) : edgeComponent e=edgeComponent f := by
  have aux {a b : OrientedEdge G} (h : Relation.EqvGen TrackStep a b) :
      edgeComponent a=edgeComponent (E.mapEdge e) →
      ∀ a' b' : OrientedEdge H,E.mapEdge a'=a → E.mapEdge b'=b → edgeComponent a'=edgeComponent b' := by
    induction h with
    | rel a b h =>
      intro _ a' b' ha hb
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ ((E.track_step_iff a' b').mpr (by rw [ha,hb]; exact h))
    | refl a =>
      intro _ a' b' ha hb
      exact congrArg edgeComponent (E.mapEdge_injective (ha.trans hb.symm))
    | symm a b h ih =>
      intro hb a' b' ha' hb'
      have ha : edgeComponent a=edgeComponent (E.mapEdge e) := (Quotient.sound h).trans hb
      exact (ih ha b' a' hb' ha').symm
    | trans a b c hab hbc ihab ihbc =>
      intro ha a' c' ha' hc'
      have hb : edgeComponent b=edgeComponent (E.mapEdge e) := (Quotient.sound hab).symm.trans ha
      obtain ⟨b',hb'⟩ := hretained b hb
      exact (ihab ha a' b' ha' hb').trans (ihbc hb b' c' hb' hc')
  exact aux (Quotient.exact hcomp) rfl e f rfl rfl

theorem crossing_map {c d : TrackComponent H} (h : ComponentCrosses c d) :
    ComponentCrosses (E.componentMap c) (E.componentMap d) := by
  obtain ⟨C,h⟩ := h
  refine ⟨E.mapCell C,?_⟩
  rcases h with ⟨hc,hd⟩ | ⟨hc,hd⟩
  · left
    constructor
    · change E.componentMap (edgeComponent C.edgeAB)=E.componentMap c
      rw [hc]
    · change E.componentMap (edgeComponent C.edgeAD)=E.componentMap d
      rw [hd]
  · right
    constructor
    · change E.componentMap (edgeComponent C.edgeAB)=E.componentMap d
      rw [hc]
    · change E.componentMap (edgeComponent C.edgeAD)=E.componentMap c
      rw [hd]

theorem source_of_source_map (e : OrientedEdge H) (hs : SpineSource (E.mapEdge e)) : SpineSource e := by
  rintro ⟨f,hf⟩
  exact hs ⟨E.mapEdge f,(E.positive_step_iff f e).mp hf⟩

end L38HalfPentagonEmbedding
end Swanepoel
