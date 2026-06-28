function arch_rise(curvature){
	if (curvature){
		if (curvature == 0)
			return 0.001;

		return curvature;
	}
	return 0.2;
}

class Canvas {
	constructor(x0, y0, x1, y1, color, dir, curvature){
		curvature = arch_rise(curvature);

		if (!dir)
			dir = 1;
		Object.assign(this, {x0, y0, x1, y1, color, dir, curvature});
	}

	get dx(){
		if (this._dx == null){
			this._dx = this.x1 - this.x0;
		}

		return this._dx;
	}

	get dy(){
		if (this._dy == null){
			this._dy = this.y1 - this.y0;
		}

		return this._dy;
	}

	get width(){
		if (this._width == null){
			this._width = this.x_max - this.x_min;
		}

		return this._width;
	}

	get height(){
		if (this._height == null){
			this._height = this.y_max - this.y_min;
		}

		return this._height;
	}

	get alpha(){
		if (this._alpha == null){
			//within (-PI, PI]
			if (this.dir > 0)
				this._alpha = this.theta(this.x0, this.y0);
			else{
				this._alpha = this.theta(this.x1, this.y1);
			}
		}

		return this._alpha;
	}

	get beta(){
		if (this._beta == null){
			//within (-PI, PI] or (PI, 3 * PI]
			if (this.dir > 0) {
				this._beta = this.theta(this.x1, this.y1);
			}
			else {
				this._beta = this.theta(this.x0, this.y0);
			}
			if (this._beta <= this.alpha){
				this._beta += Math.PI * 2;
			}
		}

		return this._beta;
	}

	get x_args(){
		if (this._x_args == null){
			var [xo, yo] = this.origin;
			//(x - xo) ** 2 + (y - yo) ** 2 = radius ** 2;
			this._x_args = [this.x0, this.x1];

			if (this.contains(0)){
				this._x_args.push(xo + this.radius);
			}

			if (this.contains(Math.PI)){
				this._x_args.push(xo - this.radius);
			}
		}

		return this._x_args;
	}

	get y_args(){
		if (this._y_args == null){
			var [xo, yo] = this.origin;
			//(x - xo) ** 2 + (y - yo) ** 2 = radius ** 2;
			this._y_args = [this.y0, this.y1];

			if (this.contains(Math.PI / 2)){
				this._y_args.push(yo + this.radius);
			}

			if (this.contains(-Math.PI / 2)){
				this._y_args.push(yo - this.radius);
			}
		}

		return this._y_args;
	}

	get	x_min(){
		if (this._x_min == null){
			this._x_min = Math.min(...this.x_args) - 4;
		}

		return this._x_min;
	}

	get	x_max(){
		if (this._x_max == null){
			this._x_max = Math.max(...this.x_args) + 4;
		}

		return this._x_max;
	}

	get y_min(){
		if (this._y_min == null){
			this._y_min = Math.min(...this.y_args) - 4;
		}

		return this._y_min;
	}

	get y_max(){
		if (this._y_max == null){
			this._y_max = Math.max(...this.y_args) + 4;
		}

		return this._y_max;
	}

	get center(){
		if (this._center == null){
			this._center = [(this.x0 + this.x1) / 2, (this.y0 + this.y1) / 2];
		}

		return this._center;
	}

	get origin(){
		if (this._origin == null){
			var [xo, yo] = this.center;
			//(y - yo) / (x - xo) = (y1 - yo) / (x1 - xo);
			var theta = Math.atan2(this.y0 - yo, this.x0 - xo);

			if (this.dir > 0)
				theta -= Math.PI / 2;
			else
				theta += Math.PI / 2;

			var delta = this.delta;
			this._origin = [xo + delta * Math.cos(theta), yo + delta * Math.sin(theta)];
		}

		return this._origin;
	}

	get delta(){
		if (this._delta == null){
			//http://www.lemma.cn/py/?module=Algebra.Eq.of.Eq_Add_Sqrt.radical_Conjugate
			this._delta = this.distance * (1 / this.curvature - this.curvature) / 4;
		}
		return this._delta;
	}

	get	radius(){
		if (this._radius == null){
			var d = this.distance / 2;
			var delta = this.delta;
			this._radius = Math.sqrt(delta * delta + d * d);
		}
		return this._radius;
	}

	get distance(){
		if (this._distance == null){
			this._distance = distance(this.x0, this.y0, this.x1, this.y1);
		}

		return this._distance;
	}

	contains(theta, strict){
		var {alpha, beta} = this;
		if (theta < alpha){
			theta += Math.PI * 2;
		}

		if (theta > beta){
			theta -= Math.PI * 2;
		}

		if (strict){
			var epsilon = (beta - alpha) / 100;
			return theta > alpha + epsilon && theta < beta - epsilon;
		}

		return theta >= alpha && theta <= beta;
	}

	theta(x, y){
		var [xo, yo] = this.origin;
		return Math.atan2(y - yo, x - xo);
	}

	drawDashedLine(ctx){
		ctx.beginPath();
        ctx.setLineDash([5, 10, 15]);
    	ctx.moveTo(this.x0, this.y0);
    	ctx.lineTo(this.x1, this.y1);
		ctx.stroke();
	}

	drawArc(ctx, x0, y0){
		ctx.beginPath();

        var [xo, yo] = this.origin;

		xo -= x0;
		yo -= y0;

        ctx.arc(xo, yo, this.radius, this.alpha, this.beta);

		ctx.stroke();
	}

	drawRect(ctx, x0, y0){
		ctx.beginPath();

        ctx.rect(this.x0 - x0, this.y0 - y0, this.dx, this.dy);

		ctx.stroke();
	}

	drawArrow(ctx, x0, y0){
		ctx.beginPath();
      	//draw the ending point:
    	var x1 = this.x1;
    	var y1 = this.y1;

		x1 -= x0;
		y1 -= y0;
        var dx = 5;
        var dy = dx * 1.5;
        var delta = Math.PI / 8;
		var beta = this.dir > 0 ? this.beta - Math.PI / 2:this.alpha + Math.PI / 2;

    	ctx.moveTo(x1, y1);
		ctx.lineTo(x1 + dy * Math.cos(beta + delta), y1 + dy * Math.sin(beta + delta));
    	ctx.lineTo(x1 + dy * Math.cos(beta - delta), y1 + dy * Math.sin(beta - delta));

    	ctx.fill();
	}

	drawArrowedArc(ctx){
		this.set_color(ctx);
        this.drawArc(ctx, this.x_min, this.y_min);
        this.drawArrow(ctx, this.x_min, this.y_min);
	}

	clearArc(ctx, x0, y0){
		if (this.x1 == null)
			return;
		//source = picture to draw;
		//destination = picture drawn;
		ctx.globalCompositeOperation = "source-out"; //draw picture outside the already-drawn;

		this.drawArc(ctx, x0, y0);
		this.x1 = this.y1 = null;

		ctx.globalCompositeOperation = "source-over";//draw picture over the already-drawn;
	}

	clearDashedLine(ctx){
		if (this.x1 == null)
			return;
		//source = picture to draw;
		//destination = picture drawn;
		ctx.globalCompositeOperation = "source-out"; //draw picture outside the already-drawn;

		this.drawDashedLine(ctx);
		this.x1 = this.y1 = null;

		ctx.globalCompositeOperation = "source-over";//draw picture over the already-drawn;
	}

	clearRect(ctx, x0, y0){
		if (this.x1 == null)
			return;
		//source = picture to draw;
		//destination = picture drawn;
		ctx.globalCompositeOperation = "source-out"; //draw picture outside the already-drawn;
		this.drawRect(ctx, x0, y0);
		this.x1 = this.y1 = null;
		ctx.globalCompositeOperation = "source-over";//draw picture over the already-drawn;
	}

	set_color(ctx){
		ctx.strokeStyle = this.color;
		ctx.fillStyle = this.color;
		ctx.lineWidth = 1;
	}

	distance_between_arc_and_point(x, y){
		var theta = this.theta(x, y);

		if (this.contains(theta)){
			var [xo, yo] = this.origin;
			var dx = xo - x;
			var dy = yo - y;
			return Math.abs(Math.sqrt(dx * dx + dy * dy) - this.radius);
		}
		else{
			var dx0 = x - this.x0;
			var dy0 = y - this.y0;

			var dx1 = x - this.x1;
			var dy1 = y - this.y1;

			var d0 = Math.sqrt(dx0 * dx0 + dy0 * dy0);
			var d1 = Math.sqrt(dx1 * dx1 + dy1 * dy1);
			return Math.min(d0, d1);
		}
	}

	offset(dx, dy){
		var sector = new Canvas(this.x0 + dx, this.y0 + dy, this.x1 + dx, this.y1 + dy, this.color);
		sector._origin = [this.origin[0] + dx, this.origin[1] + dy];
		sector._radius = this.radius;

		sector._alpha = this.alpha;
		sector._beta = this.beta;

		return sector;
	}

	is_intersected_with(that){
		var d = distance(...this.origin, ...that.origin);
		if (d >= this.radius + that.radius)
			return false;

		var p = this.radius + that.radius + d;
		p /= 2;
		//Heron's triangle formula
		var s = Math.sqrt(p * (p - this.radius) * (p - that.radius) * (p - d));
		var delta = s * 2 / d;

		var alpha0 = Math.asin(delta / this.radius);
		var dx = that.origin[0] - this.origin[0];
		var dy = that.origin[1] - this.origin[1];
		var theta0 = Math.atan2(dy, dx);

		var alpha1 = Math.asin(delta / that.radius);
		var theta1 = theta0 + Math.PI;

		if (this.contains(theta0 + alpha0, true) && that.contains(theta1 - alpha1, true) || this.contains(theta0 - alpha0, true) && that.contains(theta1 + alpha1, true)){
			return [dx / 5, dy / 5];
		}
	}

	clear_cache(){
		for (var key of Object.keys(this)){
			if (key.startsWith('_') && this[key] != null)
				delete this[key];
		}
	}

	shift_x0(dx, codonCell){
		var {row, col, index} = this;

		var x0 = codonCell[row][col].x0[index];
		if (dx >= 0){
			var x0_max = codonCell[row][col].x0_max[index];
			if (x0 + dx > x0_max){
				dx = x0_max - x0;
			}
		}
		else {
			var x0_min = codonCell[row][col].x0_min[index];
			if (x0 + dx < x0_min){
				dx = x0_min - x0;
			}
		}

		this.x0 += dx;
		this.clear_cache();

		codonCell[row][col].x0[index] += dx;
	}

	shift_x1(dx, codonCell){
		var {row, col, index} = this;
		var x1 = codonCell[row][col].x1[index];
		if (dx >= 0){
			var x1_max = codonCell[row][col].x1_max[index];
			if (x1 + dx > x1_max){
				dx = x1_max - x1;
			}
		}
		else {
			var x1_min = codonCell[row][col].x1_min[index];
			if (x1 + dx < x1_min){
				dx = x1_min - x1;
			}
		}

		this.x1 += dx;
		this.clear_cache();
		codonCell[row][col].x1[index] += dx;
	}
}

console.log('import Canvas.js');

export default Canvas