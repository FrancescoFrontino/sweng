sig User {

}

sig Vehicle{
s: one Status
}

sig Time{
}

sig Ride{
u: one User,
v: one Vehicle,
ts: set TravelStop,
td: set TravelDrive,
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

// ad ogni veicolo è associato uno status diverso
fact noSameStatusDifferentVehicles{
all v1,v2: Vehicle | (v1 != v2) => (v1.s != v2.s)
}

// nessun time associato alla ride
pred noRideAssociated[t: Time]{
no r:Ride | r.time = t
}

// non esiste un tempo senza una ride associata
fact noTimeWithoutRide{
all t: Time | not(noRideAssociated[t])
}

pred show(){
#User > 2
#Ride > 2
#Vehicle > 4
}

run show for 5
