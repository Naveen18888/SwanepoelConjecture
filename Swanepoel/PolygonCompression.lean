module
public import Swanepoel.PolygonArea
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def stepDoubleArea (p : Plane) (ds : List Plane) : ℝ :=
  match ds with
  | [] => 0
  | d::rest => cross2 p (p+d)+stepDoubleArea (p+d) rest

def nonzeroSteps (ds : List Plane) : List Plane := ds.filter (fun d => decide (d≠0))

theorem nonzeroSteps_cons (d : Plane) (ds : List Plane) :
    nonzeroSteps (d::ds)=if d=0 then nonzeroSteps ds else d::nonzeroSteps ds := by
  by_cases hd : d=0 <;> simp [nonzeroSteps,hd]

def stepEnergy (ds : List Plane) : ℝ := (ds.map (fun d => ‖d‖^2)).sum

def stepLength (ds : List Plane) : ℝ := (ds.map (fun d => ‖d‖)).sum

theorem nonzeroSteps_sum (ds : List Plane) : (nonzeroSteps ds).sum=ds.sum := by
  induction ds with
  | nil => simp [nonzeroSteps]
  | cons d ds ih =>
    by_cases hd : d=0
    · simp [nonzeroSteps_cons,hd,ih]
    · simp [nonzeroSteps_cons,hd,ih]

theorem stepDoubleArea_nonzeroSteps (p : Plane) (ds : List Plane) :
    stepDoubleArea p (nonzeroSteps ds)=stepDoubleArea p ds := by
  induction ds generalizing p with
  | nil => simp [nonzeroSteps,stepDoubleArea]
  | cons d ds ih =>
    by_cases hd : d=0
    · simp [nonzeroSteps_cons,hd,stepDoubleArea,cross2_self,ih]
    · simp [nonzeroSteps_cons,hd,stepDoubleArea,ih]

theorem stepEnergy_nonzeroSteps (ds : List Plane) :
    stepEnergy (nonzeroSteps ds)=stepEnergy ds := by
  induction ds with
  | nil => simp [stepEnergy,nonzeroSteps]
  | cons d ds ih =>
    simp only [stepEnergy] at ih ⊢
    by_cases hd : d=0 <;> simp [nonzeroSteps_cons,hd,ih]

theorem stepLength_nonzeroSteps (ds : List Plane) :
    stepLength (nonzeroSteps ds)=stepLength ds := by
  induction ds with
  | nil => simp [stepLength,nonzeroSteps]
  | cons d ds ih =>
    simp only [stepLength] at ih ⊢
    by_cases hd : d=0 <;> simp [nonzeroSteps_cons,hd,ih]

theorem nonzeroSteps_are_unit (ds : List Plane)
    (hsteps : ∀ d∈ds, d=0 ∨ ‖d‖=1) :
    ∀ d∈nonzeroSteps ds, ‖d‖=1 := by
  intro d hd
  have hmem := List.mem_filter.mp hd
  have hne : d≠0 := of_decide_eq_true hmem.2
  exact (hsteps d hmem.1).resolve_left hne

theorem unit_stepEnergy (ds : List Plane) (hunit : ∀ d∈ds, ‖d‖=1) :
    stepEnergy ds=ds.length := by
  induction ds with
  | nil => simp [stepEnergy]
  | cons d ds ih =>
    have hd := hunit d (by simp)
    have ht : ∀ e∈ds, ‖e‖=1 := fun e he => hunit e (by simp [he])
    simp only [stepEnergy,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [hd]
    have hi := ih ht
    change (1 : ℝ)^2+stepEnergy ds=(ds.length : ℝ)+1
    rw [hi]
    ring

theorem unit_stepLength (ds : List Plane) (hunit : ∀ d∈ds, ‖d‖=1) :
    stepLength ds=ds.length := by
  induction ds with
  | nil => simp [stepLength]
  | cons d ds ih =>
    have hd := hunit d (by simp)
    have ht : ∀ e∈ds, ‖e‖=1 := fun e he => hunit e (by simp [he])
    simp only [stepLength,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [hd]
    have hi := ih ht
    change (1 : ℝ)+stepLength ds=(ds.length : ℝ)+1
    rw [hi]
    ring

theorem zero_or_unit_energy_eq_active_count (ds : List Plane)
    (hsteps : ∀ d∈ds, d=0 ∨ ‖d‖=1) :
    stepEnergy ds=(nonzeroSteps ds).length := by
  rw [← stepEnergy_nonzeroSteps]
  exact unit_stepEnergy _ (nonzeroSteps_are_unit ds hsteps)

theorem zero_or_unit_length_eq_active_count (ds : List Plane)
    (hsteps : ∀ d∈ds, d=0 ∨ ‖d‖=1) :
    stepLength ds=(nonzeroSteps ds).length := by
  rw [← stepLength_nonzeroSteps]
  exact unit_stepLength _ (nonzeroSteps_are_unit ds hsteps)

end Swanepoel
