import java.util.ArrayList;

public class Distributor{
	
	/*
	 * COME FUNZIONA LA COSA?
	 * 1) L'ALGORITMO TIENE SEMPRE AGGIORNATO IL VALORE DELLA DISTANZA MEDIA (AVG) FRA TUTTI I VEICOLI
	 * 2) PER OGNI MACCHINA SOGGETTA AD UNO SPOSTAMENTO ATTO A GARANTIRE UNA DISTRIBUZIONE EQUA
	 * 		VIENE IDENTIFICATA LA MACCHINA A DISTANZA MINORE
	 * 3) VIENE IDENTIFICATO COME PARCHEGGIO "GIUSTO" QUELLO A DISTANZA (AVG) DALLA MACCHINA PIU' VICINA.
	 * 		LA DIREZIONE E' CASUALE.
	 * 
	 * L'OBIETTIVO E' QUELLO DI TENERE LE MACCHINE LONTANE DAI GRANDI AGGLOMERATI DI ALTRE AUTO.
	 */
	
	private ArrayList<Car> cars;
	private int averageDistance;

	public Distributor(){
		this.cars = new ArrayList<>();
		this.averageDistance = 0;
	}
	
	public void addCar(Car car){
		this.cars.add(car);
	}
	
	public Car getCar(int idx){
		return this.cars.get(idx);
	}
	
	// calcola la media delle distanze tra le macchine
	private void calculateAverageDistance(){
		
		int tot = 0;
		int dist;
		
		for(int i=0; i<cars.size()-1; i++){
			for(int j=i+1; j<cars.size(); j++){
				dist = distanceBetweenCars(cars.get(i), cars.get(j));
				tot += dist;
				//System.out.println("Distanza da " + i + " a " + j + " :" + dist);
			}
		}
		
		//System.out.println("Somma delle distanze: " + tot);
		
		tot /= cars.size();
		this.averageDistance = tot;
	}
	
	
	// restituisce l'auto più vicina alla macchina c
	private Car findNearestCar(Car c){
		int minDist = 0;
		Car found = null;
		
		for(Car car : cars){
			if(minDist == 0){
				minDist = distanceBetweenCars(c, car);
				found = car;
			}
			else
				if(distanceBetweenCars(c, car) < minDist && !car.equals(c)){
					minDist = distanceBetweenCars(c, car);
					found = car;
				}
		}
		
		//System.out.println("Distanza dalla macchina più vicina: " + minDist);
		
		return found;
	}
	
	// genera un nuovo valore della x per la macchina
	private int getNewX(Car c){
		
		int valX;
		int X_UPPERBOUND = 800;
		
		do{
			valX = c.getX();
			int signX = (int) (Math.random()*10%2);
			int incX = (int) (Math.random()*1000%20);
			
			if(signX == 0)
				valX -= incX;
			else
				valX += incX;
		}while(valX > X_UPPERBOUND || valX < 0);
		
		return valX;	
	}
	
	// genera un nuovo valore della y per la macchina
	private int getNewY(Car c){
		int valY;
		int Y_UPPERBOUND = 600;
		
		
		do{
			valY = c.getY();
			int signY = (int) (Math.random()*10%2);
			int incY = (int) (Math.random()*1000%20);
			
			if(signY == 0)
				valY -= incY;
			else
				valY += incY;
		}while(valY > Y_UPPERBOUND || valY < 0);
		
		return valY;
				
	}
	
	// calcola la distanza euclidea fra due veicoli
	private int distanceBetweenCars(Car c1, Car c2){
		float distance;
		
		distance = (float) Math.sqrt(Math.pow(c2.getX()-c1.getX(),2) + Math.pow(c2.getY()-c1.getY(),2));
		
		return (int)distance;
	}

	// data una macchina c, le trova una collocazione che garantisca una distribuzione equa
	public void findNewPosition(Car c){
		
		Car nearestCar = null;
		
		calculateAverageDistance();
		//System.out.println("Distanza media: " + this.averageDistance);
		nearestCar = findNearestCar(c);
		c.move(getNewX(nearestCar), getNewY(nearestCar));
	}
}