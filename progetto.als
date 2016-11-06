sig User {

}

sig Vehicle{

}

sig Time{
}

sig Ride{
u: one User,
v: one Vehicle,
ts: some TravelStop,
td: some TravelDrive,
time: one Time
}

abstract sig Travel{
}

sig TravelStop extends Travel{
}

sig TravelDrive extends Travel{
}

sig Status{
}

sig Infrazione{
}

// non esiste un tempo a cui sono associate più corse
fact noMoreRidesOneTime{
no r1,r2: Ride | r1 != r2 && r1.v = r2.v && r1.time = r2.time
}

// non deve esserci un utente associato a più corse nello stesso tempo
fact noMoreRidesOneTimeSameUser{
no r1,r2: Ride | r1 != r2 && r1.u = r2.u && r1.time = r2.time
}

// non esistono tratte in comune a più corse
fact noSameTravelMoreRides{
no r1,r2: Ride | r1 != r2 && (r1.ts = r2.ts || r1.td = r2.td)
}

pred show(){
#User > 2
#Ride > 2
#Vehicle > 4
}

run show for 5
