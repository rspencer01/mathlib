/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.opposites

/-!
# The Yoneda embedding

The Yoneda embedding as a functor `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)`,
along with an instance that it is `fully_faithful`.

Also the Yoneda lemma, `yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`.
-/

namespace category_theory
open opposite

universes v₁ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

def yoneda : C ⥤ (Cᵒᵖ ⥤ Sort v₁) :=
{ obj := λ X,
  { obj := λ Y, unop Y ⟶ X,
    map := λ Y Y' f g, f.unop ≫ g,
    map_comp' := λ _ _ _ f g, begin ext1, dsimp, erw [category.assoc] end,
    map_id' := λ Y, begin ext1, dsimp, erw [category.id_comp] end },
  map := λ X X' f, { app := λ Y g, g ≫ f } }

def coyoneda : Cᵒᵖ ⥤ (C ⥤ Sort v₁) :=
{ obj := λ X,
  { obj := λ Y, unop X ⟶ Y,
    map := λ Y Y' f g, g ≫ f,
    map_comp' := λ _ _ _ f g, begin ext1, dsimp, erw [category.assoc] end,
    map_id' := λ Y, begin ext1, dsimp, erw [category.comp_id] end },
  map := λ X X' f, { app := λ Y g, f.unop ≫ g },
  map_comp' := λ _ _ _ f g, begin ext1, ext1, dsimp, erw [category.assoc] end,
  map_id' := λ X, begin ext1, ext1, dsimp, erw [category.id_comp] end }

namespace yoneda
@[simp] lemma obj_obj (X : C) (Y : Cᵒᵖ) : (yoneda.obj X).obj Y = (unop Y ⟶ X) := rfl
@[simp] lemma obj_map (X : C) {Y Y' : Cᵒᵖ} (f : Y ⟶ Y') :
  (yoneda.obj X).map f = λ g, f.unop ≫ g := rfl
@[simp] lemma map_app {X X' : C} (f : X ⟶ X') (Y : Cᵒᵖ) :
  (yoneda.map f).app Y = λ g, g ≫ f := rfl

lemma obj_map_id {X Y : C} (f : op X ⟶ op Y) :
  ((@yoneda C _).obj X).map f (𝟙 X) = ((@yoneda C _).map f.unop).app (op Y) (𝟙 Y) :=
by obviously

@[simp] lemma naturality {X Y : C} (α : yoneda.obj X ⟶ yoneda.obj Y)
  {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) : f ≫ α.app (op Z') h = α.app (op Z) (f ≫ h) :=
begin erw [functor_to_types.naturality], refl end

instance yoneda_full : full (@yoneda C _) :=
{ preimage := λ X Y f, (f.app (op X)) (𝟙 X) }
instance yoneda_faithful : faithful (@yoneda C _) :=
{ injectivity' := λ X Y f g p,
  begin
    injection p with h,
    convert (congr_fun (congr_fun h (op X)) (𝟙 X)); dsimp; simp,
  end }

/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply yoneda.ext,
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C)
  (p : Π {Z : C}, (Z ⟶ X) → (Z ⟶ Y)) (q : Π {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
  (h₁ : Π {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : Π {Z : C} (f : Z ⟶ Y), p (q f) = f)
  (n : Π {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
@preimage_iso _ _ _ _ yoneda _ _ _ _
  (nat_iso.of_components (λ Z, { hom := p, inv := q, }) (by tidy))

def is_iso {X Y : C} (f : X ⟶ Y) [is_iso (yoneda.map f)] : is_iso f :=
is_iso_of_fully_faithful yoneda f

end yoneda

namespace coyoneda

@[simp] lemma obj_obj (X : Cᵒᵖ) (Y : C) : (coyoneda.obj X).obj Y = (unop X ⟶ Y) := rfl
@[simp] lemma obj_map {X' X : C} (f : X' ⟶ X) (Y : Cᵒᵖ) :
  (coyoneda.obj Y).map f = λ g, g ≫ f := rfl
@[simp] lemma map_app (X : C) {Y Y' : Cᵒᵖ} (f : Y ⟶ Y') :
  (coyoneda.map f).app X = λ g, f.unop ≫ g := rfl

@[simp] lemma naturality {X Y : Cᵒᵖ} (α : coyoneda.obj X ⟶ coyoneda.obj Y)
  {Z Z' : C} (f : Z' ⟶ Z) (h : unop X ⟶ Z') : (α.app Z' h) ≫ f = α.app Z (h ≫ f) :=
begin erw [functor_to_types.naturality], refl end

instance coyoneda_full : full (@coyoneda C _) :=
{ preimage := λ X Y f, ((f.app (unop X)) (𝟙 _)).op }
instance coyoneda_faithful : faithful (@coyoneda C _) :=
{ injectivity' := λ X Y f g p,
  begin
    injection p with h,
    have t := (congr_fun (congr_fun h (unop X)) (𝟙 _)),
    simpa using congr_arg has_hom.hom.op t,
  end }

def is_iso {X Y : Cᵒᵖ} (f : X ⟶ Y) [is_iso (coyoneda.map f)] : is_iso f :=
is_iso_of_fully_faithful coyoneda f

end coyoneda

class representable (F : Cᵒᵖ ⥤ Sort v₁) :=
(X : C)
(w : yoneda.obj X ≅ F)

end category_theory

namespace category_theory
-- For the rest of the file, we are using product categories,
-- so need to restrict to the case morphisms are in 'Type', not 'Sort'.

universes v₁ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

open opposite

variables (C : Type u₁) [𝒞 : category.{v₁+1} C]
include 𝒞

-- We need to help typeclass inference with some awkward universe levels here.
instance prod_category_instance_1 : category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
category_theory.prod.{(max u₁ v₁) v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

instance prod_category_instance_2 : category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
category_theory.prod.{v₁ (max u₁ v₁)} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

open yoneda

def yoneda_evaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
evaluation_uncurried Cᵒᵖ (Type v₁) ⋙ ulift_functor.{u₁}

@[simp] lemma yoneda_evaluation_map_down
  (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (x : (yoneda_evaluation C).obj P) :
  ((yoneda_evaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) := rfl

def yoneda_pairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ functor.hom (Cᵒᵖ ⥤ Type v₁)

@[simp] lemma yoneda_pairing_map
  (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : (yoneda_pairing C).obj P) :
  (yoneda_pairing C).map α β = yoneda.map α.1.unop ≫ β ≫ α.2 := rfl

def yoneda_lemma : yoneda_pairing C ≅ yoneda_evaluation C :=
{ hom :=
  { app := λ F x, ulift.up ((x.app F.1) (𝟙 (unop F.1))),
    naturality' :=
    begin
      intros X Y f, ext1, ext1,
      cases f, cases Y, cases X,
      dsimp,
      erw [category.id_comp,
           ←functor_to_types.naturality,
           obj_map_id,
           functor_to_types.naturality,
           functor_to_types.map_id]
    end },
  inv :=
  { app := λ F x,
    { app := λ X a, (F.2.map a.op) x.down,
      naturality' :=
      begin
        intros X Y f, ext1,
        cases x, cases F,
        dsimp,
        erw [functor_to_types.map_comp]
      end },
    naturality' :=
    begin
      intros X Y f, ext1, ext1, ext1,
      cases x, cases f, cases Y, cases X,
      dsimp,
      erw [←functor_to_types.naturality, functor_to_types.map_comp]
    end },
  hom_inv_id' :=
  begin
    ext1, ext1, ext1, ext1, cases X, dsimp,
    erw [←functor_to_types.naturality,
         obj_map_id,
         functor_to_types.naturality,
         functor_to_types.map_id],
    refl,
  end,
  inv_hom_id' :=
  begin
    ext1, ext1, ext1,
    cases x, cases X,
    dsimp,
    erw [functor_to_types.map_id]
  end }.

variables {C}

@[simp] def yoneda_sections (X : C) (F : Cᵒᵖ ⥤ Type v₁) : (yoneda.obj X ⟶ F) ≅ ulift.{u₁} (F.obj (op X)) :=
(yoneda_lemma C).app (op X, F)

omit 𝒞
@[simp] def yoneda_sections_small {C : Type u₁} [small_category C] (X : C) (F : Cᵒᵖ ⥤ Type u₁) : (yoneda.obj X ⟶ F) ≅ F.obj (op X) :=
yoneda_sections X F ≪≫ ulift_trivial _

end category_theory
