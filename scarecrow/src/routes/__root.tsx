import { Link, Outlet, createRootRoute } from "@tanstack/react-router";

export const Route = createRootRoute({
  component: RootComponent,
});

function RootComponent() {
  return (
    <>
      <div className="p-2 flex gap-2 bg-white">
        <Link to="/" className="[&.active]:font-bold hover:underline">
          Index
        </Link>
      </div>
      <hr />
      <div className="m-2 w-fit">
        <Outlet />
      </div>
    </>
  );
}
