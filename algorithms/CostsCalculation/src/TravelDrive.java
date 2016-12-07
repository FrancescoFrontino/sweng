import java.util.Calendar;

public class TravelDrive {
	private int passengersNumber;
	private Calendar startTime;
	private Calendar endTime;
	private final float PASSENGERS_BONUS = (float) 0.1;
	private final float COST_PER_MINUTE = (float) 0.3;
	
	
	public TravelDrive(int passengersNumber){
		this.startTime.getTime();
		this.passengersNumber = passengersNumber;
	}
	
	public void endTravel(){
		this.endTime.getTime();
	}
	
	public boolean deservePassengersBonus() {
		return this.passengersNumber > 3;
	}
	
	public float calculateCosts(){
		
		float minutes;
		float cost;
		
		minutes = (endTime.getTimeInMillis() * 1000 / 60 - startTime.getTimeInMillis() * 1000 / 60);
		cost = minutes * COST_PER_MINUTE;
		
		if(this.deservePassengersBonus())
			cost-= cost * PASSENGERS_BONUS;
		
		return cost;
	}
}