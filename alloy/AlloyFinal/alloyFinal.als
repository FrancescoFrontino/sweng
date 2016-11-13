open util/boolean



//----------------SIGNATURE---------------------


sig User {}

sig Car{ 
	status: one CarStatus  
}

sig CarStatus{ 
	tag: one Tag,
	batteryLow: lone Bool,
	distanceGreater: lone Bool,
	passengerNumber: one Int,
}{
	(tag=ONROAD) => (passengerNumber>0 && passengerNumber<=4) 
	(tag!=ONROAD) => (passengerNumber=0) 
	(distanceGreater != none ) <=> (tag = AVAILABLE)
	(batteryLow != none ) <=> (tag = AVAILABLE)
}


abstract sig Tag {}
one sig AVAILABLE extends Tag {}
one sig BATTERYCHARGE extends Tag {}
one sig BOOKED extends Tag {}
one sig PARKING extends Tag {}
one sig ONROAD extends Tag {}


sig Reservation{
	user: one User,
	car: one Car,
	expired: one Bool,
	ride:lone Ride
}{ 
	(expired=False) =>(ride!=none) || (ride=none && car.status.tag=BOOKED)
	(expired=True) => (car.status.tag = AVAILABLE || car.status.tag = BATTERYCHARGE)  
}

sig Ride{
	user: one User,
	car: one Car,
	stop: some TravelStop,
	drive: some TravelDrive,
	finalStatus: lone CarStatus,
	violation:some Violation,
	chargeBonus: one Bool, 
	batteryBonus: one Bool, 
	negativeBonus: one Bool
}{
	(finalStatus!=none) <=> (finalStatus.tag=AVAILABLE || finalStatus.tag=BATTERYCHARGE)
	chargeBonus=True <=>	finalStatus.tag=BATTERYCHARGE	
	batteryBonus=True <=> (finalStatus.tag=AVAILABLE && finalStatus.batteryLow=False)	 //?
	negativeBonus=True <=>(finalStatus.distanceGreater=True || finalStatus.batteryLow=True)
}

abstract sig Travel{
	carStatus : some CarStatus
}{
	#carStatus=2 
}

sig TravelStop extends Travel{
}{
	carStatus.tag = PARKING
}

sig TravelDrive extends Travel{
	passengerBonus: one Bool 
}{
	carStatus.tag = ONROAD
	(passengerBonus=True) <=> (carStatus.passengerNumber=3 || carStatus.passengerNumber=4)
}

sig Violation{ }


//----------------FACT---------------------


//esiste un solo finalStatus associato ad ogni ride
fact oneFinalStatusForRide{
	no r1,r2:Ride | r1!=r2 && r1.finalStatus=r2.finalStatus
}

//non esistono prenotazioni associate a due utenti e alla stessa macchina
fact noMoreUserAndCarSameReservation{
	no r1,r2:Reservation| (r1!=r2) && (r1.user=r2.user)
	no r1,r2:Reservation|(r1!=r2) && (r1.car=r2.car)
}

//non esistono due utenti e due macchine con una stessa ride
fact noMoreUserAndCarSameRide{
	no r1,r2:Ride| (r1!=r2) && (r1.user=r2.user)
	no r1,r2:Ride|(r1!=r2) && (r1.car=r2.car)
}

//Ad ogni reservation not expired corrisponde una sola ride relativa alla stessa macchina e allo stesso utente
fact noRideWithoutReservation{
	no res1,res2:Reservation | res1 != res2 && res1.ride=res2.ride
	all ride:Ride| userReservation[ride.user] 
	all r:Ride,res:Reservation | (r.user=res.user) => (r.car=res.car)
	no r:Ride,res:Reservation | res.ride = r && res.user != r.user
}

pred userReservation[user1:User]{ 
	one reservation:Reservation | reservation.user=user1 && reservation.expired=False 
}

//ogni violation è univoca
fact noMoreRideSameViolation{ 	
	no disjoint r1,r2:Ride | r1.violation & r2.violation !=none 
}

//ogni ride è composta da tratte univoche

fact noMoreRideSameTravel{
	no disjoint r1,r2:Ride | r1.stop & r2.stop != none
	no disjoint r1,r2:Ride | r1.drive & r2.drive != none  
	all travelStop:TravelStop | notAloneStop[travelStop]
	all travelDrive:TravelDrive | notAloneDrive[travelDrive]
}

pred notAloneStop[travelStop:TravelStop]{
 	one ride:Ride | ride.stop&travelStop!=none
}

pred notAloneDrive[travelDrive:TravelDrive]{	
	one ride:Ride | ride.drive&travelDrive!=none
}

//ogni macchina ha il suo carStatus
fact noMoreCarSameStatus{
	no car1,car2:Car | car1!=car2  && car1.status=car2.status
	all carStatus:CarStatus | notAloneStatus[carStatus]
	all car:Car | statusUnique[car]
}


pred notAloneStatus[carStatus1:CarStatus ]{	
	(one travel:Travel | travel.carStatus&carStatus1!=none) ||
	(one car:Car | car.status&carStatus1!=none) 
}


//non esistono macchine che hanno uno stato di una prenotazione legata ad un altra macchina

pred statusUnique[car1:Car]{
	no ride:Ride| ride.car!=car1 && (car1.status&ride.stop.carStatus!=none) 
	no ride:Ride| ride.car!=car1 && (car1.status&ride.drive.carStatus!=none)
	no ride:Ride| ride.car!=car1 && (car1.status&ride.finalStatus!=none)
}

//non esistono tratte con lo stesso stato e lo stato si riferisce alla macchina della prenotazione

fact noMoreTravelSameStatusAndDifferentCar{
	no disjoint ts1,ts2: TravelStop | ts1!=ts2 && ts1.carStatus & ts2.carStatus !=none
	no disjoint td1,td2: TravelDrive | td1!=td2 && td1.carStatus & td2.carStatus !=none
	no disjoint td1: TravelDrive,ts2: TravelStop |   td1.carStatus & ts2.carStatus !=none
}

//non esistono macchine on road non appartanenti ad una prenotazione o ad una ride
fact noCarsOnRoadNotBelongingToReservationOrRide{
	no c: Car  | noReservationOrRide[c] && c.status.tag = ONROAD
	no c: Car  | noReservationOrRide[c]  &&  c.status.tag = PARKING
	no c: Car  | noReservationOrRide[c]  &&  c.status.tag = BOOKED
}

pred noReservationOrRide[c: Car]{
	no res: Reservation, ride: Ride | res.car = c || ride.car = c
}


//----------------RUN---------------------


//assertion bonus batteria e passeggeri, sia fact che assertion

assert bonusMeansEndRide{
no r: Ride | r.batteryBonus = True && r.finalStatus = none
no r: Ride | r.chargeBonus = True && r.finalStatus = none
no r: Ride | r.negativeBonus = True && r.finalStatus = none

all r: Ride | (r.chargeBonus = True) implies (r.car.status.tag = BATTERYCHARGE)
all r: Ride | (r.batteryBonus = True) implies (r.car.status.tag = AVAILABLE && r.car.status.batteryLow = False)
all r: Ride | (r.negativeBonus = True) implies (r.car.status.batteryLow = True || (r.car.status.distanceGreater = True))
}

check bonusMeansEndRide


// una volta che la prenotazione sia scaduta non vi è modo di annullare l'effetto ( no ride assertion )
assert expiredReservationImpliesNoRide{
all res: Reservation | (res.expired = True) implies (noRideRelated[res])
}

pred noRideRelated[res: Reservation]{
no r: Ride | r = res.ride
}

check expiredReservationImpliesNoRide

//se ho una ride significa che la prenotazione non è scaduta
assert rideMeansNoExpiredReservation{
all r: Ride | reservationRelated[r]
}

pred reservationRelated[r: Ride]{
one res: Reservation | res.ride = r && res.expired = False
}  

check rideMeansNoExpiredReservation


//----------------RUN---------------------

pred show(){/*
	//for special cases
	all ride:Ride | #ride.violation <=1 
	lone ride:Ride | ride.finalStatus!=none && ride.batteryBonus=True 
	lone ride:Ride | ride.finalStatus!=none && ride.chargeBonus =True
	one ride:Ride | ride.finalStatus!=none && ride.drive.passengerBonus = True 
	one res:Reservation| res.expired=False && res.car.status.tag = BOOKED	*/
}

run show for 10 but 1 Violation 
