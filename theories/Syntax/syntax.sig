typ : Type
exp(Vari) : Type
bool : Type

Bool : typ
Arr : typ -> typ -> typ

BLit : bool -> exp
Abs : typ -> (bind exp in exp) -> exp
App : exp -> exp -> exp
