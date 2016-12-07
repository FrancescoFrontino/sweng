import java.util.ArrayList;

public class Ride {
	
	private ArrayList<TravelDrive> travelDrives;
	private ArrayList<TravelStop> travelStops;
	private boolean finalCharge;
	private final float CHARGE_BONUS = (float) 0.2;
	
	public Ride(){
		this.travelDrives = new ArrayList<>();
		this.travelStops = new ArrayList<>();
		this.finalCharge = false;
	}
	
	public float calculateTotalCosts(){
		float cost = 0;
		
		for(int i=0; i<travelDrives.size(); i++)
			cost+=travelDrives.get(i).calculateCosts();
		
		for(int i=0; i<travelStops.size(); i++)
			cost+=travelStops.get(i).calculateCosts();
		
		if(this.finalCharge)
			cost-=cost*CHARGE_BONUS;
		
		return cost;
	}
	
	public void putCarInCharge(){
		this.finalCharge = true;
	}
}