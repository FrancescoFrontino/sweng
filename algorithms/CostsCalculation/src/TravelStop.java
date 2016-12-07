import java.util.Calendar;

public class TravelStop {
	private Calendar startTime;
	private Calendar endTime;
	private final float COST_PER_MINUTE = (float) 0.1;
	private boolean inCharge;
	
	public TravelStop(){
		this.startTime.getTime();
		this.inCharge = false;
	}
	
	public void endTravel(){
		this.endTime.getTime();
	}
	
	
	public float calculateCosts(){
		
		float minutes;
		float cost;
		
		minutes = (endTime.getTimeInMillis() * 1000 / 60 - startTime.getTimeInMillis() * 1000 / 60);
		cost = minutes * COST_PER_MINUTE;;
		
		return cost;
	}
}
