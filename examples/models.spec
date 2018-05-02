{-@
data Creditcard = Creditcard
	{ creditcardNumber :: String
	, creditcardHolder :: String
	}
@-}

{-@
data EntityField Creditcard typ where 
   Models.CreditcardNumber :: EntityField Creditcard {v:_ | True}
 | Models.CreditcardHolder :: EntityField Creditcard {v:_ | True}
 | Models.CreditcardId :: EntityField Creditcard {v:_ | True}
@-}