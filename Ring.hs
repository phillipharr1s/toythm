
zee = "Z" :. K 0

predicate = "" :. F "Z" :> K 0

eq = "=" :. ("" :. F "Z" :> "" :. F "Z" :> K 0)

refl = "refl" :. (fromNamed $
  "x" :. F "Z" :>
  F "=" :@ F "x" :@ F "x"
  )

eqElim = "eqElim" :. (fromNamed $ 
  "P" :. predicate :> 
  "x" :. F "Z" :>
  "y" :. F "Z" :> 
  "x=y" :. (F "=" :@ F "x" :@ F "y") :> 
  "Px" :. (F "P" :@ F "x") :> 
  F "P" :@ F "y"
  )

zero = "0" :. F "Z"

one = "1" :. F "Z"

opA = fromNamed $ "" :. F "Z" :> "" :. F "Z" :> F "Z"

add = "+" :. opA

mul = "*" :. opA

comm = fromNamed $ 
  "op" :. opA :\ 
  "x" :. F "Z" :> 
  "y" :. F "Z" :> 
  F "=" 
  :@ (F "op" :@ F "x" :@ F "y") 
  :@ (F "op" :@ F "y" :@ F "x")

assoc = fromNamed $ 
  "op" :. opA :\ 
  "x" :. F "Z" :> 
  "y" :. F "Z" :> 
  "z" :. F "Z" :> 
  F "=" 
  :@ (F "op" :@ (F "op" :@ F "x" :@ F "y") :@ F "z") 
  :@ (F "op" :@ F "x" :@ (F "op" :@ F "y" :@ F "z"))

addComm = "+com" :. (nf $ comm :@ F "+")

mulComm = "*com" :. (nf $ comm :@ F "*")

addAssoc = "+assoc" :. (nf $ assoc :@ F "+")

mulAssoc = "*assoc" :. (nf $ assoc :@ F "*")

unit0 = ("unit0" :.) $ fromNamed $
  "x" :. F "Z" :>
  F "=" 
  :@ (F "+" :@ F "0" :@ F "x")
  :@ (F "x")

unit1 = ("unit1" :.) $ fromNamed $ 
  "x" :. F "Z" :>
  F "="
  :@ (F "*" :@ F "1" :@ F "x")
  :@ (F "x")
  

dist = ("dist" :.) $
  "x" :. F "Z" :>
  "y" :. F "Z" :>
  "z" :. F "Z" :>
  F "="
  :@ (F "*" :@ F "x" :@ (F "+" :@ F "y" :@ F "z"))
  :@ (F "+" :@ (F "*" :@ F "x" :@ F "z") :@ (F "*" :@ F "x" :@ F "z"))

ring = reverse $ 
  [ zee
  , eq
  , refl
  , eqElim
  , zero
  , one
  , add
  , mul
  , addComm
  , mulComm
  , addAssoc
  , mulAssoc
  , unit0 
  , unit1
  , dist
  ]

eqTrans = fromNamed $ 
  "x" :. F "Z" :\
  "y" :. F "Z" :\
  "z" :. F "Z" :\
  "x=y" :. (F "=" :@ F "x" :@ F "y") :\
  "y=z" :. (F "=" :@ F "y" :@ F "z") :\
  F "eqElim" 
  :@ ("q" :. F "Z" :\ (F "=" :@ F "x" :@ F "q"))
  :@ F "y"
  :@ F "z"
  :@ F "y=z" 
  :@ F "x=y"