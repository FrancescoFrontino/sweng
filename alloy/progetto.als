open util/boolean

sig User {}

sig Car{ status: one CarStatus  }

sig CarStatus{ car: one Car  }

sig EndRideStatus extends CarStatus{
	inCharge: one Bool,
	batteryLow: one Bool,
	distanceGreater: one Bool
}

sig Reservation{
	user: one User,
	car: one Car,
	expired: one Bool,
	ride:lone Ride
}{ (ride!=none) <=> (expired=False) }



sig Ride{
	user: one User,
	car: one Car,
	stop: some TravelStop,
	drive: some TravelDrive,
	end: one EndRideStatus,
	violation:some Violation,
	chargeBonus: one Bool, 
	batteryBonus: one Bool, 
	negativeBonus: one Bool
}{
	chargeBonus=True <=>	end.inCharge=True	
	batteryBonus=True <=>  end.batteryLow=False	
	negativeBonus=True <=>(end.distanceGreater=True || end.batteryLow=True)
}


abstract sig Travel{
	carStatus : some CarStatus
}{ #carStatus=2 }

sig TravelStop extends Travel{}

sig TravelDrive extends Travel{	passengerBonus: one Bool }
sig Violation{}

//esiste un solo endride associato ad ogni ride
fact oneEndRideForRide{
	all endRide:EndRideStatus | existEndRide[endRide]
	all ride:Ride | ride.end.car = ride.car
	no disjoint stop:TravelStop, end:EndRideStatus | stop.carStatus & end != none
	no disjoint drive:TravelDrive, end:EndRideStatus | drive.carStatus & end != none
}

pred existEndRide[endRide:EndRideStatus]{ one ride:Ride | ride.end = endRide }


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
	no reservation1,reservation2:Reservation | reservation1 != reservation2 && reservation1.ride=reservation2.ride
	all ride:Ride| userReservation[ride.user] 
	all r:Ride,res:Reservation | (r.user=res.user) => (r.car=res.car)
	no r:Ride,res:Reservation | res.ride = r && res.user != r.user
}

pred userReservation[user1:User]{ one reservation:Reservation | reservation.user=user1 && reservation.expired=False }

//ogni violation è univoca
fact noMoreRideSameViolation{ 	no disjoint r1,r2:Ride | r1.violation & r2.violation !=none }

//ogni ride è composta da tratte univoche 
fact noMoreRideSameTravel{
	no disjoint r1,r2:Ride | r1.stop & r2.stop != none
	no disjoint r1,r2:Ride | r1.drive & r2.drive != none  
	all travelStop:TravelStop | notAloneStop[travelStop]
	all travelDrive:TravelDrive | notAloneDrive[travelDrive]
}

pred notAloneStop[travelStop:TravelStop]{
 one ride:Ride | ride.stop = travelStop
 }

pred notAloneDrive[travelDrive:TravelDrive]{	
one ride:Ride | ride.drive = travelDrive 
}

//ogni macchina ha il suo carStatus
fact noMoreCarSameStatus{
	no car1,car2:Car | car1!=car2  && car1.status=car2.status
	all carStatus:CarStatus | statusUnique[carStatus]

}
/*
pred carBooked[car1:Car]{
	one res: Reservation | res.car =car1
}

pred noStatusWithoutTravel[status:CarStatus]{
	some trs:TravelStop, trd:TravelDrive | ( trs.carStatus=status ||  trd.carStatus=status )
}*/

pred statusUnique[ carStatus:CarStatus]{
	no car1:Car| carStatus.car!=car1 && car1.status = carStatus
}


//non esistono tratte con lo stesso stato e lo stato si riferisce alla macchina della prenotazione
fact noMoreTravelSameStatusAndDifferentCar{
	no disjoint ts1,ts2: TravelStop | ts1!=ts2 && ts1.carStatus & ts2.carStatus !=none
	no disjoint td1,td2: TravelDrive | td1!=td2 && td1.carStatus & td2.carStatus !=none
	no disjoint td1: TravelDrive,ts2: TravelStop |   td1.carStatus & ts2.carStatus !=none
	no ride:Ride,trs:TravelStop | ride.stop = trs && ride.car != trs.carStatus.car 
	no ride:Ride,trd:TravelDrive | ride.drive =trd && ride.car!= trd.carStatus.car
}




pred show(){
//	some r: Reservation | r.expired = True
//	some s: CarStatus | s.batteryLow = False
	//one r:Ride| r.chargeBonus =False
	//#Violation = 3

	#Reservation =1
 	
	//#TravelDrive = 0
	//#TravelStop = 0
}

run show for 10
