
public class Car {
	private int x;
	private int y;
	
	// confini della città intesi in un range (0, k)
	private final int X_UPPERBOUND = 800;
	private final int Y_UPPERBOUND = 600;
	
	public Car(){
		this.x = (int) (Math.random()*1000 % X_UPPERBOUND);
		this.y = (int) (Math.random()*1000 % Y_UPPERBOUND);
	}
	
	
	// muove la macchina casualmente entro i confini della città
	public void move(){
		
		int valX;
		int valY;
		
		do{
			valX = this.x;
			int signX = (int) (Math.random()*10%2);
			int incX = (int) (Math.random()*1000%120);
			
			if(signX == 0)
				valX -= incX;
			else
				valX += incX;
		}while(valX > X_UPPERBOUND || valX < 0);
		
		do{
			valY = this.y;
			int signY = (int) (Math.random()*10%2);
			int incY = (int) (Math.random()*1000%120);
			
			if(signY == 0)
				valY -= incY;
			else
				valY += incY;
		}while(valY > Y_UPPERBOUND || valY < 0);
		
		
		this.x = valX;
		this.y = valY;
	}
	
	public int getX(){
		return this.x;
	}
	
	public int getY(){
		return this.y;
	}
	
	// muove la macchina in una posizione specifica
	public void move(int x, int y){
		this.x = x;
		this.y = y;
	}
}
